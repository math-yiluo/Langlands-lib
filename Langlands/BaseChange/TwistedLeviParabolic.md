# Standard parabolics of Levi products and their induced σ-intertwiners

The module `Langlands.BaseChange.TwistedLeviParabolic` (namespace
`Langlands.BaseChange.TwistedLeviPaleyWiener`) describes parabolic induction
inside a Levi product `M_B = ∏ᵢ GL_{Bᵢ}(E)` of `GL_n(E)` and its twisting
operator for an algebra automorphism `σ` acting entrywise. It is the setting of
the induction over Levi subgroups in Rogawski (1988), §11, where the theorem
for `GL_n(E)` is reduced to the same theorem on its proper Levi subgroups.

## Definitions

Let `B` and `C` be block shapes of `n` and `E` a commutative ring. The three
constructions below are defined for every commutative ring `E` and all `B`
and `C`.

- `relParabolic E B C : Subgroup (B.Levi E)` is the preimage of the standard
  upper block parabolic `C.parabolic E` under the block-diagonal embedding
  `B.leviEmbedding E`.
- `relEmbedding E B C` sends an element of `relParabolic E B C` to its
  block-diagonal matrix in `C.parabolic E`.
- `relProjection E B C : relParabolic E B C →* C.Levi E` is
  `C.leviProjection E ∘ relEmbedding E B C`: it extracts the diagonal blocks
  of `C` from the block-diagonal matrix. Without a refinement hypothesis it
  need not be surjective: for a nonzero `E`, `B = (1, 1)` and `C = (2)`,
  `relParabolic E B C`
  is all of `(Eˣ)²` and `relProjection E B C` is the diagonal embedding into
  `GL₂(E)`, whose image misses the unipotent upper triangular matrix with
  upper-right entry `1`.

The twisted trace Paley–Wiener statements use these constructions only for
pairs with `C.parabolic E ≤ B.parabolic E`, and only for a field `E`. When `E`
is nonzero (in particular a field), this inclusion holds exactly when `C`
refines `B`, that is, when every partial sum of the block sizes of `B` is a
partial sum of the block sizes of `C`. If a partial sum of `B` is not one of
`C`, some elementary matrix below the diagonal lies in `C.parabolic E` but not
in `B.parabolic E`. For a refinement `C` of `B` over a field,
`relParabolic E B C` is the intersection `P_C ∩ M_B`, the standard parabolic
subgroup of `M_B` with Levi factor `M_C`, and `relProjection E B C` is its
Levi projection. Over the zero ring every parabolic is the whole trivial
group, so the inclusion holds for all `B` and `C`. The input propositions of
`Langlands.BaseChange.TwistedLeviPaleyWienerStatements` use the subgroup
inclusion `C.parabolic E ≤ B.parabolic E` directly, and the refinement
criterion above explains this inclusion. The Library has its forward direction for cut sets:
`Langlands.Aubert.parabolic_le_of_cuts_subset` (module
`Langlands.Representation.Aubert.CutTransitionMaps`) shows, for every
commutative ring `R`, that `B.cuts ⊆ C.cuts` (every interior partial sum of
the block sizes of `B` is one of `C`) implies
`C.parabolic R ≤ B.parabolic R`.

## Compatibility with `σ`

For `σ : E ≃ₐ[F] E`, `leviAut σ B` applies `σ` to every matrix entry of every
block.

- `leviAut_mem_relParabolic_iff`: `leviAut σ B g ∈ relParabolic E B C` iff
  `g ∈ relParabolic E B C`. The proof rewrites with
  `entrywiseAut_leviEmbedding` and uses `entrywiseAut_mem_parabolic_iff`.
- `relProjection_leviAut`: the projection of `leviAut σ B x` is
  `leviAut σ C` of the projection of `x`. The block-diagonal matrix of
  `leviAut σ B x` is `entrywiseAut σ n` of that of `x`, and
  `leviProjection_entrywiseAut` gives the result.
- `continuous_leviAut` and `continuous_leviAut_symm`: if `E` has its
  `F`-module topology, `leviAut σ B` and its inverse are continuous, factor by
  factor, by `continuous_entrywiseAut_of_isModuleTopology` (applied to `σ` and
  to `σ.symm`).

## The induced σ-intertwiner

`relInducedSigmaIntertwiner σ B C Ξ BΞ` is, for a representation `Ξ` of `M_C`
and an isomorphism `BΞ : Ξ ≅ Ξ ∘ leviAut σ C`, the isomorphism from the
unnormalized smooth induction
`Induction.smoothInduced (relParabolic E B C) (Ξ.comp (relProjection E B C))`
to its pullback by `leviAut σ B`, given by

```text
(ι f)(g) = BΞ (f ((leviAut σ B)⁻¹ g))
```

(`eval_relInducedSigmaIntertwiner`, which holds by definition). It is the
Library's generic `inducedTwistedIntertwiner` for the data above. This is the
operator of Rogawski (1988), §3, printed p. 218, and Henniart–Lemaire (2011),
II.4.4, printed p. 85, in the unnormalized model; for the one-block shape
`B` it is the operator `TwistedPaleyWiener.inducedSigmaIntertwiner` of
`GL_n(E)` transported to the Levi product.
