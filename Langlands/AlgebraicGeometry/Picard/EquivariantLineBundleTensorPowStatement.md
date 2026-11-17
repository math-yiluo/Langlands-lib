# Equivariant structures on tensor powers of equivariant line bundles

Author: Worker 3462.

`Langlands.AlgebraicGeometry.Picard.EquivariantLineBundleTensorPowStatement.{u}`
quantifies over an actual étale equivalence relation `E` in the scheme
universe `u`, an actual equivariant line bundle `B : EquivariantLineBundle E`
and a natural number `n`. It asserts that there is an equivariant line bundle
`B'` on the same relation together with an isomorphism of module sheaves on
the chart `E.U`

```lean
B'.bundle.obj ≅ Langlands.Scheme.Modules.tensorPow B.bundle.obj n
```

Here `tensorPow M 0` is the structure sheaf and
`tensorPow M (n + 1) = M ⊗ tensorPow M n` (the Library's definition in
`Langlands.AlgebraicGeometry.Modules.Tensor`). Only the existence of some
equivariant structure is asserted: the statement does not say how the
transport isomorphisms of `B'` are related to those of `B`, and it does not
choose `B'`. The case `n = 0` asks for an equivariant structure on a bundle
isomorphic to the structure sheaf.

## Provenance

Derived. A descent datum for a quasi-coherent module along a relation is
compatible with tensor products: if `φ : t^*L ≅ s^*L` satisfies the cocycle
condition, then `φ^{⊗n}`, composed with the canonical identifications
`t^*(L^{⊗n}) ≅ (t^*L)^{⊗n}` and `s^*(L^{⊗n}) ≅ (s^*L)^{⊗n}`, again satisfies
it. This is the routine compatibility used whenever a polarization `L` is
replaced by a power `L^{⊗n}`, for instance in the proof of fpqc locality of
relative ampleness in the Stacks Project, Lemma 74.13.1, tag
[0D3C](https://stacks.math.columbia.edu/tag/0D3C), cited by the target
`PolarizedEtaleRelationEffectivityStatement`. The Library packages descent
data as `EquivariantLineBundle`, with transports for all related pairs of
`T`-valued points and the identity, transitivity and precomposition laws;
the statement transcribes the compatibility into that interface.

## Intended use

The proof of `PolarizedEtaleRelationEffectivityStatement` obtains, from
ampleness of `B.bundle`, a section of some positive tensor power that
generates at a given point. This statement moves the equivariant structure to
that tensor power, so that the degree-one result
`EquivariantInvariantSectionStatement` can be applied to it.

This module defines the proposition only and proves nothing.
