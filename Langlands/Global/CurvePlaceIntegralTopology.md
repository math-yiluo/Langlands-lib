# Finite-module topology on actual upper completed integer rings

This helper supplies the finite, projective and topological-module properties
of the original completed integer-ring extensions used in the integral Weil
point comparison. It also supplies a general compact finite-module topology
comparison, with independent universes.

## Source and scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, passes through integral models in the global
Weil comparison. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This is derived topological infrastructure for that local integral step.
The paired consumer is `FunctionFieldIntegralWeilRestrictionTopology`.

## Compact finite topological modules

`Langlands.Global.compactFiniteModuleIsModuleTopology R M` assumes a compact
commutative topological ring `R`, a finite `R` module `M`, and a Hausdorff
topological additive group on `M` with continuous `R` action. The two types
have independent universes. It proves `IsModuleTopology R M`: the given
topology is the canonical module topology.

The proof uses a copy `ULift M` carrying the module topology, leaving the
original topology on `M` intact. The copy has continuous addition and scalar
action. A finite module over compact `R` is compact by Mathlib's finite
generator argument. The canonical linear equivalence from the copy to `M`
is continuous by the defining module-topology property. It is a bijection
from a compact space to a Hausdorff space, hence a homeomorphism. Transport
along this actual continuous linear equivalence identifies the original
topology with the module topology. This result does not assume that a
coefficient presentation of the original topology is already quotient.

## Actual completed integer-ring extensions

The remaining scoped instances lie in
`Langlands.Global.CurvePlaceIntegralTopology`.
`completedIntegerTopologicalRing` equips an actual
`curvePlaceCompletionIntegers v` with its inherited topological ring
structure by its original subring of the original completion.
`completedIntegerOpenUnits` reuses the proved
`isOpenUnits_openSubring` construction and openness of the actual valuation
subring. Thus the given unit topology is the correct open subspace topology,
including continuous inversion. These two instances need only the original
constant field, ambient field and algebra structure, with no finiteness.

For the extension instances let `k`, `K` and `L` lie in one arbitrary universe,
with finite `k`, their three algebra structures, `FiniteDimensional K L`,
`IsScalarTower k K L`, the original `RatFunc k`-algebra presentation of `K`,
its constant-field tower, and `FunctionField k K`. Fix an original lower
place `p` and any `q : CurvePlacesAbove k L p`. No separability hypothesis
is imposed.

`localFinite` derives `Module.Finite Op Oq` from the actual integral tensor
equivalence. Its source `Op tensor_R S` is finite over `Op`, because the
actual integral closure `S` is finite over `R`. The equivalence makes the
whole original upper integer product finite, and the original coordinate
projection is surjective, giving finiteness of the chosen original `Oq`.

`continuousSMul` uses continuity of the actual completed-integer embedding
and multiplication in the original upper integer ring. `moduleTopology`
then applies the generic compact finite-module theorem, using the proved
compactness of the original lower completed integer ring. Its conclusion
compares the original upper subspace topology to the finite-module topology;
no topology is transported into place by assumption.

`localProjective` uses the proved finite module and torsion-freeness of the
original integer-ring action over the lower DVR. The finite torsion-free
module over this principal ideal domain is free and hence projective, using
Mathlib's existing instances.

These instances prepare the integral Weil point homeomorphism. They do not
assert existence of global models or the adelic comparison.
