# Canonical adelic Weil comparison in both characteristics

This statement records the conclusion of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2,
printed pp.9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The natural comparison

    (Res_(L/K) X)(A_K) → X(A_L)

is a homeomorphism for the independently constructed adelic topologies.
The two endpoint point sets consist of actual scheme morphisms from
the spectra of the original adele rings over their original fields.
The representing scheme is the published `affineChartWeilRestriction`;
its glued construction represents the Weil restriction of the supplied
quasi-projective scheme.

`NumberFieldAdelicProjectiveWeilComparisonStatement` quantifies over
number fields K and L with the specified algebra map K → L. Such an
extension is finite. The full adele rings retain all infinite factors.
The geometric inputs are an actual quasi-compact scheme X and an
immersion j : X → P^n_L, with arbitrary n including zero. X is equipped
with the structure map j followed by P^n_L → Spec L, written
`originalScheme L X n j`. Local finite type follows from this immersion.
No closed-immersion or affine restriction is imposed.

The two topologies are specified independently. For arbitrary finite
lower and upper supports U and V, the statement takes schemes P over
O(K,U) and Q over O(L,V), each with locally finite type and quasi-compact
structure map, and specified generic-fiber isomorphisms to Res_(L/K) X
and X respectively. The source topology is
`numberFieldSpreadAdelePointTopology K U P _ e`, and the target topology
is `numberFieldSpreadAdelePointTopology L V Q _ f`. No separation
hypothesis on P or Q is assumed. The conclusion is `IsHomeomorph` of
`NumberFieldProjectiveWeilAdeleEvaluation.adelicEvaluation`. That
function is the original field Weil counit evaluated along the literal
full adele inclusion, with its proved diagonal-coefficient compatibility.
It has no integral-model or spread parameter.

`CurvePlaceAdelicProjectiveWeilComparisonStatement` has the parallel
conclusion for function fields over a finite field k. The inputs are
compatible k- and K-algebra structures on L, a specified compatible
function-field presentation of K over RatFunc k, and finite degree
[L:K]. The RatFunc k-algebra structure on L, its scalar towers, and its
function-field presentation are derived in the statement by composition
and transitivity of module finiteness. These are local definitions,
not additional hypotheses. The original curve places and their completed
fields define both full adele rings. The two arbitrary spread topologies
use `curvePlaceSpreadAdelePointTopology` and the original S-integer
rings at the independently supplied supports. The map is
`CurvePlaceProjectiveWeilAdeleEvaluation.adelicEvaluation`, namely the
original field counit along `curvePlaceAdeleInclusion`. Finite L/K may
be inseparable.

`AdelicProjectiveWeilComparisonStatement` is the conjunction of these
two statements in an arbitrary common universe. Neither component
takes an auxiliary arithmetic model, a parameter for a lower affine
curve chart, a comparison homeomorphism, or any continuity, injectivity
or surjectivity premise. The supplied spreads define the endpoint
topologies; they need not form an extension-compatible pair.

The source's quasi-projective finite-type hypothesis is expressed here
by quasi-compactness of X and its specified immersion into finite
projective space. This is the scope of the existing actual Weil scheme
and arithmetic model constructions. The statement is expressed directly
with the independently defined spread topologies so that it does not
define either endpoint topology by transporting along the conclusion.
A proof may construct a common arithmetic model internally, apply the
published original-field homeomorphism for independent spreads, and
use its counit identity.

This pair contains proposition definitions, not a proof of them.
Algebraic spaces and the separate full tensor-ring isomorphism remain
other targets; the statement concerns the actual scheme point map.
