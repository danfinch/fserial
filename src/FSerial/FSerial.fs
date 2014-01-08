
module FSerial

// todo: write ISO-8601 code and remove System.Xml reference
// todo: serialize DU cases which don't have values as strings?
// todo: byte[]
// todo: extensibility (put functions into types)
// todo: add compiler flag to turn on RavenDB support

open System
open System.Reflection
open Microsoft.FSharp.Reflection
open Futility
open Newtonsoft.Json
open Newtonsoft.Json.Linq

let private getFields (t : Type) =
  t.GetFields ()
  |> Array.filter (fun f -> not <| (f.IsStatic || f.IsInitOnly))
  |> Array.sortBy (fun f -> f.Name)

let private getProperties (t : Type) =
  t.GetProperties ()
  |> Array.filter (fun p -> p.CanRead && p.CanWrite  && not <| (p.GetGetMethod ()).IsStatic)
  |> Array.sortBy (fun p -> p.Name)

/// Serialize an object to a JToken.
let rec node (t : Type) (o : obj) =
  let generic = t.IsGenericType
  let gt = if generic then t.GetGenericTypeDefinition () else null
  let arg = if generic then t.GetGenericArguments().[0] else null
  let inline nodeBool (x : bool) = JValue x :> JToken
  let inline nodeInt (x : int) = JValue x :> JToken
  let inline nodeString (x : string) = JValue x :> JToken
  let inline nodeFloat (x : float) = JValue x :> JToken
  let inline nodeLong (x : int64) = JValue x :> JToken
  let inline nodeUlong (x : uint64) = JValue x :> JToken
  let inline nodeTime (x : DateTime) = JValue x :> JToken
  let inline nodeArray (at : Type) (x : obj) =
    let x = x :?> oseq
    let array = JArray ()
    for y in x do
      node at y
      |> array.Add
    array :> JToken
  
  // scalars
  if o == null then JValue (null :> obj) :> JToken
  elif t == typeof<bool> then o :?> bool |> nodeBool
  elif t == typeof<int> then o :?> int |> nodeInt
  elif t == typeof<string> then o :?> string |> nodeString
  elif t == typeof<float> then o :?> float |> nodeFloat
  elif t == typeof<int64> then o :?> int64 |> nodeLong
  elif t == typeof<uint64> then o :?> uint64 |> nodeUlong
  elif t == typeof<DateTime> then o :?> DateTime |> nodeTime
  elif t == typeof<byte> then o :?> byte |> int |> nodeInt
  elif t == typeof<sbyte> then o :?> sbyte |> int |> nodeInt
  elif t == typeof<char> then o :?> char |> string |> nodeString
  elif t == typeof<int16> then o :?> int16 |> int |> nodeInt
  elif t == typeof<uint16> then o :?> uint16 |> int |> nodeInt
  elif t == typeof<uint32> then o :?> uint32 |> int64 |> nodeLong
  elif t == typeof<int64> then o :?> int64 |> float |> nodeFloat
  elif t == typeof<uint64> then o :?> uint64 |> float |> nodeFloat
  elif t == typeof<single> then o :?> single |> float |> nodeFloat
  elif t == typeof<decimal> then o :?> decimal |> string |> nodeString
  elif t == typeof<TimeSpan> then o :?> TimeSpan |> System.Xml.XmlConvert.ToString |> nodeString
  elif t == typeof<Net.IPAddress> then o :?> Net.IPAddress |> string |> nodeString
  elif t == typeof<Guid> then o :?> Guid |> string |> nodeString
  elif t == typeof<Uri> then o :?> Uri |> string |> nodeString
  elif t.IsEnum then o |> string |> nodeString
  elif generic && gt == typedefof<_ option> then
    typedefof<_ option>.MakeGenericType [| arg |]
    |> Type.getProperty "Value"
    |> Property.getValue o
    |> node arg
  elif generic && gt == typedefof<_ Nullable> then
    typedefof<_ Nullable>.MakeGenericType [| arg |]
    |> Type.getProperty "Value"
    |> Property.getValue o
    |> node arg
  
  // arrays
  elif generic && gt == typedefof<_ seq> then o |> nodeArray arg
  elif t.IsArray then o |> nodeArray (t.GetElementType ())
  elif generic && (gt == typedefof<_ ResizeArray> || gt == typedefof<_ IResizeArray>) then
    o |> nodeArray arg
  elif generic && gt == typedefof<_ list> then o :?> oseq |> nodeArray arg
  elif t |> FSharpType.IsTuple then
    let array = JArray ()
    let add i et =
      FSharpValue.GetTupleField (o, i)
      |> node et
      |> array.Add
    t |> FSharpType.GetTupleElements
    |> Array.iteri add
    array :> JToken
  
  // dictionaries
  elif generic && (gt == typedefof<Dict<_, _>> || gt == typedefof<IDict<_, _>> || gt == typedefof<Map<_, _>>) then
    if not (arg == typeof<string>) then failwith "Only maps and dictionaries with string keys are supported."
    let jo = JObject ()
    let vt = t.GetGenericArguments().[1]
    let kvt = typedefof<Pair<_,_>> |> Type.makeGeneric [arg; vt]
    for p in o :?> oseq do
      let key = kvt.GetProperty "Key" |> Property.getValue p |> string
      let value = kvt.GetProperty "Value" |> Property.getValue p
      jo.Add (key, node vt value)
    jo :> JToken

  elif t == typeof<TypeMap> then
    let ja = JArray ()
    for p in o :?> TypeMap do
      let jo = JObject ()
      jo.["type"] <- JValue p.Key.AssemblyQualifiedName
      jo.["value"] <- p.Value |> node p.Key
      ja.Add jo
    ja :> JToken
  
  // unions
  elif t |> FSharpType.IsUnion then
    let jo = JObject ()
    let fields = JArray ()
    let case, vs =
      FSharpValue.GetUnionFields (o, t)
    jo.["case"] <- JValue case.Name
    jo.["fields"] <- fields
    let add i (f : PropertyInfo) =
      fields.Add (vs.[i] |> node f.PropertyType)
    case.GetFields () |> Array.iteri add
    jo :> JToken
  
  // records
  elif t |> FSharpType.IsRecord then
    let jo = JObject ()
    let vs = FSharpValue.GetRecordFields o
    let add i (f : PropertyInfo) =
      jo.Add (f.Name, vs.[i] |> node f.PropertyType)
    FSharpType.GetRecordFields t |> Array.iteri add
    jo :> JToken
  
  // classes/structs
  else
    let jo = JObject ()
    let addField (f : FieldInfo) = jo.[f.Name] <- f.GetValue o |> node f.FieldType
    let addProp (p : PropertyInfo) = jo.[p.Name] <- p.GetValue (o, null) |> node p.PropertyType
    getFields t |> Array.iter addField
    getProperties t |> Array.iter addProp
    jo :> JToken

/// Deserialize a JToken to an object.
let rec ofNode (t : Type) (j : JToken) =
  let generic = t.IsGenericType
  let gt = if generic then t.GetGenericTypeDefinition () else null
  let arg = if generic then t.GetGenericArguments().[0] else null
  
  // scalars
  if j.Type = JTokenType.Null then null
  elif t == typeof<bool> then let b : bool = JToken.op_Explicit j in b :> obj
  elif t == typeof<int> then j |> int :> obj
  elif t == typeof<string> then
    let s : string = JToken.op_Explicit j
    s :> obj
  elif t == typeof<float> then j |> float :> obj
  elif t == typeof<int64> then j |> int64 :> obj
  elif t == typeof<uint64> then j |> uint64 :> obj
  elif t == typeof<DateTime> then let d : DateTime = JToken.op_Explicit j in d :> obj
  elif t == typeof<byte> then j |> int |> byte :> obj
  elif t == typeof<sbyte> then j |> int |> sbyte :> obj
  elif t == typeof<char> then j |> string :> obj
  elif t == typeof<int16> then j |> int |> int16 :> obj
  elif t == typeof<uint16> then j |> int |> uint16 :> obj
  elif t == typeof<uint32> then j |> int64 |> uint32 :> obj
  elif t == typeof<int64> then j |> float |> int64 :> obj
  elif t == typeof<uint64> then j |> float |> uint64 :> obj
  elif t == typeof<single> then j |> float |> single :> obj
  elif t == typeof<decimal> then j |> string |> Decimal.Parse :> obj
  elif t == typeof<TimeSpan> then j |> string |> System.Xml.XmlConvert.ToTimeSpan :> obj
  elif t == typeof<Net.IPAddress> then j |> string |> Net.IPAddress.Parse :> obj
  elif t == typeof<Guid> then j |> string |> Guid.Parse :> obj
  elif t == typeof<Uri> then j |> string |> Uri.ofString :> obj
  elif t.IsEnum then j |> string |> Enum.ofString t
  elif generic && gt == typedefof<_ option> then
    typedefof<_ option>.MakeGenericType [| arg |]
    |> Type.createInstance [ j |> ofNode arg ]
  elif generic && gt == typedefof<_ Nullable> then
    typedefof<_ Nullable>.MakeGenericType [| arg |]
    |> Type.createInstance [ j |> ofNode arg ]
  
  // arrays
  elif generic && (gt == typedefof<_ seq> || gt == typedefof<_ ResizeArray> || gt == typedefof<_ IResizeArray>) then
    let ra =
      typedefof<_ ResizeArray>.MakeGenericType [| arg |]
      |> Type.createInstance []
      :?> Collections.IList
    j |> Seq.iter (fun e -> ra.Add (ofNode arg e) |> ignore)
    ra :> obj
  elif t.IsArray then
    let et = t.GetElementType ()
    let array = Array.CreateInstance (et, j.Values() |> Seq.length)
    for i = 0 to array.Length - 1 do
      array.SetValue (j.[i] |> ofNode et, i)
    array :> obj
  elif generic && gt == typedefof<_ list> then
    let array = Array.CreateInstance (arg, j.Values() |> Seq.length)
    for i = 0 to array.Length - 1 do
      array.SetValue (j.[i] |> ofNode arg, i)
    typedefof<_ list>.Assembly.GetType ("Microsoft.FSharp.Collections.ListModule")
    |> Type.getMethod "OfArray"
    |> Method.makeGeneric [ arg ]
    |> Method.invokeStatic [| array |]
  elif t |> FSharpType.IsTuple then
    let ets = FSharpType.GetTupleElements t
    j
    |> Seq.mapi (fun i x -> ofNode ets.[i] x)
    |> Array.ofSeq
    |> Tuple.createInstance t
  
  // dictionaries
  elif generic && (gt == typedefof<Dict<_, _>> || gt == typedefof<IDict<_, _>>) then
    if not (arg == typeof<string>) then failwith "Only dictionaries with string keys are supported."
    let ets = t.GetGenericArguments ()
    let dt = typedefof<Dict<_, _>>.MakeGenericType ets
    let dict = dt |> Type.createInstance []
    let meth = dt.GetMethod ("Add", ets)
    let jo = j :?> JObject
    for x in jo do
      meth.Invoke (dict, [| x.Key; x.Value |> ofNode arg |])
      |> ignore
    dict

  elif generic && (gt == typedefof<Map<_,_>>) then
    if not (arg == typeof<string>) then failwith "Only maps with string keys are supported."
    let vt = t.GetGenericArguments().[1]
    let tt = FSharpType.MakeTupleType [|arg; vt|]
    let jo = j :?> JObject
    let arr = Array.CreateInstance (tt, jo.Count)
    let i = ref 0
    for pair in jo do
      let inst = tt |> Type.createInstance [pair.Key; pair.Value |> ofNode vt]
      arr.SetValue (inst, !i)
      i := !i + 1
    typedefof<_ list>.Assembly.GetType ("Microsoft.FSharp.Collections.MapModule")
    |> Type.getMethod "OfArray"
    |> Method.makeGeneric [arg; vt]
    |> Method.invoke null [arr]

  elif t == typeof<TypeMap> then
    let ja = j :?> JArray
    let state = TypeMap ()
    for p in ja do
      let typ = p.["type"] |> string |> Type.GetType
      let v = p.["value"] |> ofNode typ
      state.Set (typ, v)
    state :> obj
  
  // unions
  elif t |> FSharpType.IsUnion then
    let case = j.["case"] |> string
    let uc =
      FSharpType.GetUnionCases t
      |> Array.find (fun c -> c.Name = case)
    let fs = uc.GetFields ()
    j.["fields"]
    |> Seq.mapi (fun i x -> x |> ofNode fs.[i].PropertyType)
    |> Array.ofSeq
    |> FSharpUnion.createInstance uc
  
  // records
  elif t |> FSharpType.IsRecord then
    t
    |> FSharpRecord.getFields
    |> List.map (fun f -> j.[f.Name] |> ofNode f.PropertyType)
    |> FSharpRecord.make t
  
  // classes/structs
  else
    let inst = Activator.CreateInstance t
    getFields t
    |> Seq.iter (fun f -> f.SetValue (inst, j.[f.Name] |> ofNode f.FieldType))
    getProperties t
    |> Seq.iter (fun f -> f.SetValue (inst, j.[f.Name] |> ofNode f.PropertyType, null))
    inst

/// Serialize an object to a JSON string.
let write t o =
  node t o
  |> string

/// Deserialize an object from a JSON string.
let read t j =
  j |> JToken.Parse
  |> ofNode t

/// Serialize an object to a JSON string (generic).
let serialize (o : 'a) =
  write typeof<'a> o

/// Deserialize an object from a JSON string (generic).
let deserialize s : 'a =
  read typeof<'a> s :?> 'a

module File =
  open System.IO
  /// Save an object to a JSON file.
  let write p t o =
    File.WriteAllText (p, write t o)
  /// Load an object from a JSON file.
  let read p t =
    File.ReadAllText (p)
    |> read t
  /// Save an object to a JSON file (generic).
  let save p (o : 'a) =
    File.WriteAllText (p, serialize o)
  /// Load an object from a JSON file (generic).
  let load p : 'a =
    File.ReadAllText (p)
    |> deserialize

module Binary =
  open System.IO
  open Newtonsoft.Json.Bson
  /// Serialize an object to a BSON stream.
  let write t o (s : Stream) =
    let w = new BsonWriter (s)
    (node t o).WriteTo (w, [||])
  /// Deserialize an object from a BSON stream.
  let read t (s : Stream) =
    let r = new BsonReader (s)
    JValue.ReadFrom r
    |> ofNode t
  /// Serialize an object to a BSON byte array (generic).
  let deflate (o : 'a) =
    use s = new MemoryStream ()
    let w = new BsonWriter (s)
    (node typeof<'a> o).WriteTo w
    s.Seek (0L, SeekOrigin.Begin) |> ignore
    let buf = Array.create (int s.Length) 0uy
    s.Read (buf, 0, buf.Length) |> ignore
    buf
  /// Deserialize an object from a BSON byte array (generic).
  let inflate (bs : byte array) : 'a =
    use s = new MemoryStream (bs)
    let r = new BsonReader (s)
    JValue.ReadFrom r
    |> ofNode typeof<'a>
    :?> 'a

