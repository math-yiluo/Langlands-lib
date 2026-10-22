# The compact open integral finite adeles

This module constructs the standard integral subring inside Mathlib's actual
finite adele ring of an arbitrary number field. The construction and its
properties have derived, internal provenance: they combine the published
completion bridge with elementary subring and product-topology arguments.
No separate original-literature claim is introduced here.

## Objects and scope

Let `K : Type u` have instances `[Field K] [NumberField K]`.
`Langlands.Global.FinitePlace K` is the type of nonzero prime ideals of the ring
of integers of `K`. For such a place `v`, the local field is Mathlib's
`v.adicCompletion K`, and its valuation subring is
`v.adicCompletionIntegers K`.

`Langlands.Global.FiniteAdeles K`, imported from `Langlands.Global.Adelic`, is
Mathlib's `IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K`.
It has the existing restricted-product topology relative to those local
valuation subrings and the cofinite filter.

The existing `Langlands.Global.FiniteAdelicGL.integralAdeles` construction,
its membership theorem, and its openness theorem are housed in this general
arithmetic module. The matrix-subgroup module imports them from here.
`integralFiniteAdeles K` reuses that same subring of finite adeles whose
coordinate at every finite place belongs to the local integer ring. The theorem
`mem_integralFiniteAdeles` states precisely

```text
a ∈ integralFiniteAdeles K ↔
  ∀ v : FinitePlace K, a v ∈ v.adicCompletionIntegers K.
```

The module proves that this subring is open and compact in the given finite
adele topology. All constructions and proofs allow arbitrary universe `u`.
There are no additional local compactness hypotheses.

## Local compactness and the completion topology

The helper `isCompact_adicCompletionIntegers` applies the published
`CompletionPadic.topologicalData v`. Its topology is definitionally the topology
of `v.adicCompletion K`. Installing its valuative relation and local-field
certificate therefore allows Mathlib's
`IsNonarchimedeanLocalField.isCompact_closedBall` to prove compactness of the
closed valuation ball of radius one in the completion topology itself.

The valuation used by that local-field theorem is
`ValuativeRel.valuation (v.adicCompletion K)`. The proof identifies its unit ball
with the actual completed integers. `Valuation.vle_one_iff` converts the unit-ball
inequality to the valuative relation at `1`. The bridge theorem
`CompletionPadic.topologicalData_vle` then converts this to
`Valued.v x ≤ Valued.v 1`, and preservation of `1` gives the defining condition
`Valued.v x ≤ 1` for membership in `v.adicCompletionIntegers K`.

Thus the transport uses the already proved comparison of valuation orders.
It needs no identification of their numerical normalizations, and it introduces
no new topology or completion model.

## Openness and product compactness

Each local integer ring is open by `Valued.isOpen_valuationSubring`.
`RestrictedProduct.isOpen_forall_mem` then proves the shared
`FiniteAdelicGL.isOpen_integralAdeles` theorem in the restricted-product topology.
`isOpen_integralFiniteAdeles` reuses this theorem through the defining alias.

For `isCompact_integralFiniteAdeles`, the local compactness helper first gives
`CompactSpace (v.adicCompletionIntegers K)` through
`isCompact_iff_compactSpace`. The product of these compact spaces is compact.
Mathlib's `RestrictedProduct.structureMap` sends a tuple of local integers to
its finite adele, and `RestrictedProduct.range_structureMap` identifies its
range exactly with the everywhere-integral locus.

The map is continuous by
`RestrictedProduct.isEmbedding_structureMap.continuous`.
`isCompact_range` therefore makes its range compact, proving the required
compactness of the integral subring. This uses continuity into the actual
restricted product; it does not infer compactness there from the weaker
coordinatewise topology on the full product of local fields.

## Provenance and dependencies

The subring packaging and its coordinate membership equivalence are internal
constructions. The two topological conclusions are derived from existing
Library and Mathlib results. The local-field certificate and comparison are
imported from `Langlands.Global.CompletionPadic`, whose paired Markdown records
the provenance of that published bridge. The restricted-product lemmas are in
Mathlib's `Topology/Algebra/RestrictedProduct/Basic.lean` and
`Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`; the local compact-ball
theorem is in `NumberTheory/LocalField/Basic.lean`.

Worker 105 implements the compact integral subring. Worker 74 supplies the
local compactness and restricted-product compactness helper arguments reused
here. Worker 212 prepares this explanation of the definitions, topology
comparison, and implemented proof route.
