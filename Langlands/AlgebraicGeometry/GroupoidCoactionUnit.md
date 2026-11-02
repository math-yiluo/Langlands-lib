# The invariant unit for arbitrary modules

Authors: Worker 1203 and Worker 101.

This internal step of the Serre criterion proof concerns the canonical map
`inducedUnit t N` from an invariant-ring module `N` to the invariants of its
extension of scalars `B ⊗[A] N`, where `A = invariantRing t`. It assumes
`RingEtaleEquivalenceRelation t` and acyclicity of every coaction in the
chosen module universe. The ring universe is `u`; the module universe is
`max u v`, so free modules, kernels, and scalar extensions stay within the
universe covered by the acyclicity hypothesis.

`inducedUnit_surjective_of_acyclic` uses the free module on the underlying
set of `N`, with its surjective linear-combination map to `N`. Extension of
scalars preserves surjectivity, and acyclicity makes the resulting map on
invariants surjective. Bijectivity of the free-module unit lifts the
resulting invariant to a vector in the free module. Naturality sends this
vector's image in `N` to the required invariant.

For injectivity, `inducedUnit_injective_of_free_cover` first considers an
arbitrary surjection `p : F → N` with `F` free. Tensor right exactness
applied to `ker p → F → N` and exactness of invariants give exactness at
the middle invariant module. For an element `n` whose unit vanishes,
choose a lift `z` in `F`. Naturality makes the unit of `z` lie in the
image of the induced kernel's invariants. Unit surjectivity, already proved
for arbitrary modules, lifts that invariant to an actual element `k` of
`ker p`. Injectivity of the free-module unit identifies `z` with `k` in
`F`, and consequently `n = 0`. Applying this to the free module on `N`
proves `inducedUnit_injective_of_acyclic`.

`inducedUnit_bijective_of_acyclic` combines these two results.
`inducedUnitLinearEquiv` packages the actual unit as an `A`-linear
equivalence, and `inducedUnitLinearEquiv_apply` records its underlying map.
No freeness or finite generation is required of `N` in these declarations.

The provenance is a direct internal derivation from the unchanged published
coaction and acyclicity predicates, the induced coaction and free-unit
construction, the invariant exactness helpers, and Mathlib tensor right
exactness. Source flatness needed by the invariant helpers follows from
étaleness. No geometric descent conclusion is assumed. This module does
not prove the counit isomorphism, faithful flatness, the ring pushout, or
the full Serre criterion.
