# Vanishing of primitive degree-two Čech classes, on the fibre square

Module `Langlands.AbelianScheme.PrimitiveCechVanishingTensor` (namespace
`Langlands.AbelianScheme.PrimitiveCechVanishing`).

The module `PrimitiveCechVanishing` proves `exists_coboundary` for the binary product
`A.X ⨯ A.X` of an abelian variety `A` over a field `K`. This module states and proves the same
result for the chosen fibre square `A.X ⊗ A.X` of the slice category (the fibre product), with
the projections `fst`, `snd` and the multiplication `fst * snd`.

- `tensorIsoProd A : A.X ⊗ A.X ≅ A.X ⨯ A.X` is the canonical isomorphism, compatible with the
  projections and the multiplication (`tensorIsoProd_hom_fst`, `tensorIsoProd_hom_snd`,
  `tensorIsoProd_hom_mul`).
- `injective_tensor`: on degree-two structure-sheaf cohomology, `μ^* - fst^* - snd^*` from `A` to
  `A ⊗ A` is injective. It is the composite of the corresponding map for `A ⨯ A`, injective by the
  Library's `fieldH2PrimitiveInjectivity`, with the pullback along `tensorIsoProd`, injective by
  `ArtinianH2Reduction.structurePull_injective_of_iso` (functoriality `structurePull_comp`).
- `exists_coboundary_tensor`: the statement of `exists_coboundary` with `A.X ⊗ A.X`, `fst`, `snd`
  and `fst * snd` in place of `A.X ⨯ A.X`, `prod.fst`, `prod.snd` and `mul A`. The proof is the
  proof of `exists_coboundary` with `injective_tensor` in place of `fieldH2PrimitiveInjectivity`;
  it is checked with an increased heartbeat limit (`maxHeartbeats 1600000`).

## Provenance

As for `PrimitiveCechVanishing`: the argument of Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, Harvard thesis revised 14 March 2021, proof of Proposition 2.2.4.1
(printed pp. 152–154, PDF pp. 180–182), registered as `lan-2008-pel-thesis-revision-2021`.
