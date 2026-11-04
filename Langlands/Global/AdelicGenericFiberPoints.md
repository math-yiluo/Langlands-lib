# Actual generic-fiber adelic points from a specified spread

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.6, equation (3.5.1), identifies the full-adele points of
an integer model with the adelic points of its generic fiber. Section 4,
printed p.9, transports the topology from the arithmetic-stage direct
limit to the generic-fiber points. This module supplies the actual
generic-fiber objects and point equivalences needed for that construction.

`curvePlaceModelGenericFiber` and `numberFieldModelGenericFiber` are the
actual scheme pullbacks along the spectra of the subtype inclusions of
the original outside-S integer rings into the original fields. Their
underlying schemes are not chosen replacements. The curve construction
itself needs only fields k and F with a k-algebra structure.

`CurvePlaceAdelePoints` and `NumberFieldAdelePoints` are actual relative
scheme morphisms from the spectrum of the full adele ring over the
original field. The curve coefficients use `CurvePlaceAdeleRing k F`
with its published full-field diagonal; the number coefficients use
Mathlib's full `Adeles K`, including every infinite factor, with its
existing field-algebra structure.

The two `GenericFiberAdelePointEquiv` definitions specialize the
published pullback-adjunction equivalence `ringPointBaseChangeEquiv`.
The original integer-base actions on model points are retained. In the
curve branch, `curvePlaceAdeleLevelDiagonal_eq` proves compatibility of
that action with the full-field diagonal; in the number branch this is
definitional. The inverse formulas identify the underlying morphism
with postcomposition by the actual first pullback projection. The
forward projection formulas and naturality in model morphisms follow
from this adjunction, and do not assume a point comparison theorem.

For a specified isomorphism e from the actual generic fiber of a model
X to a field-scheme Y, each `SpreadAdelePointEquiv` then postcomposes
generic-fiber points by e. The corresponding
`SpreadAdelePointTopology` induces the model's already defined arithmetic
final topology along the inverse equivalence. Its defining
`SpreadAdelePointHomeomorph` has that same equivalence. This construction
is explicitly indexed by the model and the chosen generic-fiber
isomorphism. It does not assume or assert independence of those data.

All constructions allow arbitrary nonaffine, nonseparated models and
empty S in a common arbitrary universe. For the full-field curve
diagonal and the curve adelic points, k is perfect and F is a function
field over k, with the supplied RatFunc k-algebra and compatible
k-algebra structure. This includes the source's positive-characteristic
global fields and extends the point-equivalence construction to
perfect constant fields. The number branch assumes an arbitrary number
field. Finite type, quasi-compactness and separatedness are not needed
for these pullback identities or for transporting a topology.

The construction of the specified-model topology follows the source;
the categorical packaging and the displayed broader scope are derived.
This definition unit does not prove that a spread exists, that stage
points exhaust all full-adele points, that two spreads give equal
topologies, or that this topology agrees with the independent affine
evaluation topology. Those remain separate obligations.
