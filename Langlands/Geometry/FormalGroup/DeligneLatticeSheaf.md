# Deligne's flat graded lattice sheaf and rational frame

Drinfeld (1976), §2 A, printed p.109 (PDF p.3), items 1 and 4, and the
opening of printed p.110 (PDF p.4), specify a graded flat O[Π]-sheaf η
and a K-linear isomorphism r:K^d→η^0⊗_O K. This module constructs those
data using the actual polynomial quotient O[Π] and actual module sheaves.
It does not impose the subsequent conditions (a)–(c).

`LatticePiSheaf d π X` has a genuine sheaf of modules over
`PiAlgebra d π`. Its flatness condition is `Module.Flat` for the actual
O[Π]-module stalk at every point of X. After restriction of scalars to O,
the homogeneous parts are genuine O-module sheaves with sectionwise
injective inclusions whose image modules form an internal direct sum.
Their degree-one maps commute with the inclusions and with multiplication
by the distinguished quotient element Π. Thus the grading is attached to
the actual module action, rather than to an independently chosen operator.
The homogeneous inclusions are proved to be sheaf monomorphisms.

`latticePi` constructs multiplication by Π as an O-linear sheaf map.
Its n-th iterate is proved to be multiplication by Π^n, and its d-th
iterate is multiplication by π, using the actual quotient relation.
These are consequences of the module action, not additional axioms in
the lattice data.

`rationalComponent` extends each actual section module along O→F and
then sheafifies in the category of F-modules. This is the sheaf tensor
extension used for η^i⊗_O F. `FramedLatticePiSheaf` adds an actual
isomorphism from the constant sheaf with value F^d to the rationalized
zero component. The constant sheaf is itself constructed by sheafifying
the constant presheaf. The implementation permits any commutative O and
any O-algebra field F in the same universe; the intended application
uses the ring of integers and its fraction field.

The provenance is derived: the source's flat sheaf and frame are
implemented through stalk modules, genuine sheaf subobjects and tensor
sheafification. This module does not construct u, its generation
condition, the fibre-injectivity or determinant conditions, the full
Deligne point functor, its PGL action or a representing formal scheme.
No representing or universal object is an input.
