signature PROP =
  sig
    datatype prop =                 (* A ::=            *)
        Atom of string              (*       P          *)
      | True                        (*     | T          *)
      | And of prop * prop          (*     | A1 & A2    *)
      | False                       (*     | F          *)
      | Or of prop * prop           (*     | A1 | A2    *)
      | Implies of prop * prop      (*     | A1 => A2   *)

    val Not : prop -> prop          (* ~A := A => F     *)

    val toString : prop -> string
  end

structure Prop :> PROP =
  struct
    datatype prop =
        Atom of string
      | True
      | And of prop * prop
      | False
      | Or of prop * prop
      | Implies of prop * prop

    fun Not A = Implies (A, False)

    fun toStringImp (Implies (A, B)) = toStringAndOr A ^ " => " ^ toStringImp B
      | toStringImp A = toStringAndOr A

    and toStringAndOr (And (A, B)) = toStringAtomic A ^ " & " ^ toStringAtomic B
      | toStringAndOr (Or (A, B)) = toStringAtomic A ^ " | " ^ toStringAtomic B
      | toStringAndOr A = toStringAtomic A

    and toStringAtomic (Atom s) = s
      | toStringAtomic True = "T"
      | toStringAtomic False = "F"
      | toStringAtomic A = "(" ^ toStringImp A ^ ")"

    fun toString x = toStringImp x
  end

signature G4IP =
  sig
    (* [decide A = true] iff . ===> A has a proof,
       [decide A = false] iff . ===> A has no proof *)
    (*val process_left_atom: Prop.prop list -> Prop.prop -> bool*)
    val process_right: Prop.prop list * Prop.prop list -> Prop.prop -> bool
    val decide : Prop.prop -> bool
  end

structure G4ip :> G4IP =
 struct  
    open Prop
    (* maintaining invertible and non-invertible props*)	
    (*datatype Context = ([Prop],[Prop])*)
    fun add_ctx (inv,nonInv) a = case a of
    	Atom _ => (inv,a::nonInv)
	|True => (inv,nonInv)
	|And (_,_) => (a::inv,nonInv)
	|False => ([False],[])
	|Or (_,_) => (a::inv,nonInv)
	|Implies ((Atom _),_) => (inv, a::nonInv)
	|Implies (Implies (_,_),_) => (inv, a::nonInv)
	|Implies (_,_) => (a::inv, nonInv) 

   and process_left_helper props (Atom b) (Atom a) = a = b
       |process_left_helper props (Atom b) _ = false
       |process_left_helper props (Implies ((Atom p),b)) c = process_right ([],props) (Atom p) andalso process_right (add_ctx ([],props) b) c
       |process_left_helper props (Implies (Implies (d,e),b)) c = 
       			    process_right (add_ctx (add_ctx ([],props) (Implies (e,b))) d) e
       			    		  andalso
       			    process_right (add_ctx ([],props) b) c
		    
   and process_left props prop2check acc=
       (*let
       val _= print((liststring (props)) ^ "\n")
       val _= print((liststring acc) ^"\n")
       val _= print((toString prop2check)^"\n")
       in*)
       case props of
       [] => false
       |x::xs => process_left_helper (xs@acc) x prop2check 
       	         orelse process_left xs prop2check (acc@[x])
       (*end*)

   and process_right _ True = true
    	 | process_right ctx (And (a,b)) = (process_right ctx a) andalso (process_right ctx b)
	 | process_right ctx (Implies (a,b)) = process_right (add_ctx ctx a) b
	 | process_right (And (a,b)::inv,nonInv) c = process_right (add_ctx (add_ctx (inv,nonInv) a) b) c
         | process_right (False::_,_) _ = true
	 | process_right (True::inv,nonInv) c = process_right (inv,nonInv) c
	 | process_right (Or (a,b)::inv,nonInv) c = process_right (add_ctx (inv,nonInv) a) c andalso process_right (add_ctx (inv,nonInv) b) c
	 | process_right (Implies (True,b)::inv,nonInv) c = process_right (add_ctx (inv,nonInv) b) c
	 | process_right (Implies (False,_)::inv,nonInv) c = process_right (inv,nonInv) c
	 | process_right (Implies (And (d,e),b)::inv,nonInv) c = process_right (add_ctx (inv,nonInv) (Implies (Implies (d,e),b))) c
	 | process_right (Implies (Or(d,e),b)::inv,nonInv) c = process_right (add_ctx (add_ctx (inv,nonInv) (Implies(d,b))) (Implies(e,b))) c
	 | process_right ([], nonInv) (Or(a,b)) = process_left nonInv (Or(a,b)) [] orelse process_right ([],nonInv) a orelse process_right ([],nonInv) b (*non-invertible or intro rules*) 	
	 | process_right ([], nonInv) a= process_left nonInv a [] (*non-invertible imp imp rule*)
	 
    and print_bool x = case x of true => print "true" | false => print "false"
    and liststring l = case l of
    	 [] => ""
        | x::xs => toString(x) ^ " *** " ^ (liststring(xs))
 
    fun decide inputProp = process_right ([],[]) inputProp

    (* maintaining invertible and non-invertible props*)
    (*datatype Context = ([Prop],[Prop])*)

    (*fun process_right ctx inputProp = true*)
 end
