# Relative Jacquet modules of Levi products and their σ-intertwiners

The module `Langlands.BaseChange.TwistedLeviJacquet` defines the unnormalized
Jacquet module of a representation of a Levi product `M_B = B.Levi E` of
`GL_n(E)` with respect to the standard parabolic `relParabolic E B C` of a
refinement `C` of `B`. It also defines the descent of σ-intertwiners to these
modules. The relative parabolic and its projection are defined in
`Langlands.BaseChange.TwistedLeviParabolic`. All declarations are in the
namespace `Langlands.BaseChange.TwistedLeviPaleyWiener`.

## Refinements and the block diagonal section

Let `B C : BlockShape n` with `hCB : C.parabolic E ≤ B.parabolic E`.

- `cuts_subset_of_parabolic_le` (any nontrivial commutative ring `E`): the
  cuts of `B` (its partial sums of block sizes) are cuts of `C`. A
  permutation matrix lies in a standard parabolic exactly when the
  permutation lies in the block Weyl group (`permutation_mem_parabolic_iff`).
  So the block Weyl group of `C` is contained in that of `B`, and
  `blockWeyl_le_iff_cuts_subset` turns this into the inclusion of cuts.
- `leviSubgroup_le_of_parabolic_le` (same generality): every block diagonal
  matrix of shape `C` is block diagonal of shape `B`, that is
  `C.leviSubgroup E ≤ B.leviSubgroup E`. By
  `Aubert.exists_refinement_of_cuts_subset`, `C` is the flattening of a
  refinement of `B`. The flattened Levi identification `flattenedLeviEquiv`
  then writes each fine block diagonal matrix as a coarse one.
- `relLeviSection_embedding` (`E` a field): for `m : C.Levi E`, the block
  diagonal matrix of shape `B` of `relLeviSection hCB m` is the block
  diagonal matrix of shape `C` of `m`. The section
  `relLeviSection hCB : C.Levi E →* relParabolic E B C` and its splitting
  property `relProjection_section` are defined and proved in
  `Langlands.BaseChange.TwistedLeviInductionTransferProof`. The section takes the
  coarse diagonal blocks of the fine block diagonal matrix of `m`. By the
  previous item that matrix is block diagonal of shape `B`, so it is recovered
  from these blocks. Thus `relLeviSection hCB` is the actual block diagonal
  inclusion `M_C ⊂ M_B`.

## The relative Jacquet module

Let `ρ` be a complex representation of `M_B` on `W`. Write
`N = (relProjection E B C).ker`. It is the subgroup of the relative parabolic
whose diagonal blocks of shape `C` are identity matrices. For a refinement
over a field, it is the unipotent radical of the relative parabolic.

- `RelJacquetModule C ρ` is
  `Jacquet.Coinvariants (ρ.comp (relParabolic E B C).subtype) N`: the
  quotient of `W` by the span of the vectors `ρ(u) x - x` with `u ∈ N`.
  `relJacquetMk C ρ` is the quotient map.
- `relJacquet hCB ρ` is the representation of `C.Levi E` on this quotient
  given by `m · [x] = [ρ(relLeviSection hCB m) x]` (`relJacquet_mk`). It is
  the action of the relative parabolic on the coinvariants
  (`Representation.toCoinvariants`) composed with the section. No modulus
  factor occurs: this is the unnormalized Jacquet module.

## The descended σ-intertwiner

Let `σ : E ≃ₐ[F] E` and let `leviAut σ B` be its entrywise action on `M_B`.

- `relParabolicAut σ B C` is the restriction of `leviAut σ B` to the relative
  parabolic. This uses `leviAut_mem_relParabolic_iff`.
- `relParabolicAut_mem_ker_iff`: the restriction preserves `N`, because
  `relProjection E B C` intertwines the entrywise actions
  (`relProjection_leviAut`).
- `relParabolicAut_relLeviSection`: the restriction commutes with the section,
  `relParabolicAut σ B C (relLeviSection hCB m) = relLeviSection hCB (leviAut σ C m)`.
  This follows from `relLeviSection_embedding` and the compatibility of the
  entrywise action with block diagonal embeddings
  (`entrywiseAut_leviEmbedding`).
- For `A : ρ.Equiv (ρ.comp (leviAut σ B).toMonoidHom)`, that is, a linear
  isomorphism with `A ρ(g) = ρ(σ g) A`, `relJacquetSigmaIntertwiner σ hCB A`
  is the linear equivalence `Jacquet.twistedCoinvariantsEquiv` of the
  quotient, `[x] ↦ [A x]` (`relJacquetSigmaIntertwiner_mk`). It intertwines
  `relJacquet hCB ρ` with its composite with `leviAut σ C`. Indeed
  `A ρ(s(m)) x = ρ(σ(s(m))) A x = ρ(s(σ m)) A x` for the section `s`.

`RelJacquetModule`, `relJacquetMk`, `relParabolicAut` and
`relParabolicAut_mem_ker_iff` are stated over a commutative ring `E`. The
declarations that use the section assume that `E` is a field, as
`relLeviSection` does.

## Comparison with the source

This is the relative form of the twisted Jacquet module of Rogawski (1988),
§3, printed p. 218. There, for `ε`-stable standard Levi subgroups `L ⊂ M` and an
`M*`-module `π`, the space `V(N)` is `ε`-stable because `ε(N) = N`, so `ε`
acts on `V_N = V/V(N)`, and this makes `r_{LM}(π)` an `L*`-module. Here
`M = M_B`, `L = M_C` (embedded by `relLeviSection`), `N` is the kernel of
`relProjection E B C`, and `ε` is the entrywise action of `σ`. The
operator `π(ε)` is replaced by an arbitrary intertwiner `A`, and its descent
is the map `[x] ↦ [A x]`.

Rogawski's Jacquet functor is normalized: `m ∈ L` acts on `V_N` by
`δ_N(m)^{-1/2} π(m)`, with `δ_N` the modulus character of `L` acting on `N`.
This module uses the unnormalized action and does not define the normalized
one. The same operator `[x] ↦ [A x]` also intertwines the normalized action
when `δ_N ∘ σ = δ_N`. This holds for the entrywise action, a topological
automorphism of `N`: `δ_N(σ(m))` is the modulus of `σ ∘ Ad(m) ∘ σ⁻¹` on `N`,
and the modulus is a homomorphism on the automorphisms of `N`, so it equals
`δ_N(m)`.

The single-group analogue, for `GL_n(E)` and a standard block parabolic, is
`Langlands.BaseChange.jacquetSigmaIntertwiner` in
`Langlands.BaseChange.TwistedJacquet`, built from the same
`Jacquet.twistedCoinvariantsEquiv`.

## Source

- J. D. Rogawski, *Trace Paley–Wiener theorem in the twisted case*, Trans.
  Amer. Math. Soc. 309 (1988), 215–229. Literature ID
  `rogawski-1988-twisted-trace-paley-wiener`, SHA-256
  `86fbe930fc1db80a3a0f279db5d83af85b7e37dc7e041d813ebc9f5fdcb7c274`; §3,
  printed p. 218 (PDF p. 4).
