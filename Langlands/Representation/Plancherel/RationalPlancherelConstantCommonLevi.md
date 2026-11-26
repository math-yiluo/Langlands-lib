# The rank-one factors of `c(G|M)` on the parabolics of one semistandard Levi

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed
p.241 (PDF p.7), registered as `waldspurger-2003-plancherel`, defines

`c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)`.

This notation presupposes that the product does not depend on the
parabolic `P` with Levi `M`. This module proves that independence for the
published Lean objects of `RationalPlancherelConstant`. These are the
index set `rankOneCocharacterSet i ζ`, made of the submodules
`rankOneCocharacters i ζ β = X_*(A_β)` for the positive roots `β` of
`ζ`; the constants `rankOneGamma i ζ K hK N`, the common-compact
open-cell constants of `P(ζ) ∩ M_N` and `U(ζ⁻¹) ∩ M_N` in the submodule
centralizer `M_N`; and their product `rankOneGammaProduct`. The argument
is derived.

## Setting

`F` is a nonarchimedean local field, `G` is connected reductive over `F`
with affine structure morphism, locally of finite type, and
`i : S → G` is a maximal split torus. `K` is a compact open subgroup of
`G(F)`. The two cocharacters `ζ, ζ'` of `S` have pairings vanishing at
the same relative roots. Where stated, `K` is stable under the dynamic
limit of `P(ξ)` for every cocharacter `ξ` of `S`.

## Declarations

- `oppositeCocharacter_groupHom_comp`: the opposite of `groupHom ν ≫ i`
  is `groupHom (-ν) ≫ i` (the published
  `groupHom_neg_comp_eq_oppositeCocharacter`).
- `rankOneGamma_add_of_mem`: for `ν ∈ N`,
  `rankOneGamma i (ζ + ν) K hK N = rankOneGamma i ζ K hK N`. Points of
  `M_N` centralize `ν` and `-ν` (`mem_cocharacterSubmoduleCentralizer`).
  The published shift lemmas
  `Dynamic.mem_parabolic_add_iff_of_mem_centralizer` and
  `Dynamic.mem_unipotent_add_iff_of_mem_centralizer` therefore leave
  `P ∩ M_N` and `U⁻ ∩ M_N` unchanged. The published
  `compactNormalizedSourceGamma_eq_of_transport` with the identity map
  concludes.
- `rankOneGamma_neg`: under limit stability of `K`,
  `rankOneGamma i (-ζ) K hK N = rankOneGamma i ζ K hK N`. The proof
  follows the published `rankOneGamma_ne_top`. By
  `exists_dynamicCentralizer_eq_cocharacterSubmoduleCentralizer`, `M_N`
  is the centralizer of one cocharacter `ψ`, and it is represented by
  the closed, smooth, connected reductive centralizer scheme
  `Dynamic.Affine.centralizerScheme ψ`. Reductivity is
  `DynamicOppositeStandardIntertwining.parameterScheme_isConnectedReductive`.
  `ζ` factors through this scheme by `Dynamic.intersectionCocharacter`.
  The published `leviGamma_eq_gamma_of_isClosedSubgroup` turns both
  rank-one constants into source gammas there, for the factored
  cocharacter and its opposite, at the preimage compact
  `closedSubgroupCompact`. The published `gamma_oppositeCocharacter`
  identifies these two gammas.
  It needs limit stability of the preimage compact for both
  cocharacters. By `compact_split_iff_limit_stable`, this is the
  splitting `m u ∈ K ↔ m ∈ K ∧ u ∈ K`. That splitting is transported from
  `G(F)` along the closed embedding, using
  `Dynamic.centralizer_le_comap` and `Dynamic.unipotent_le_comap`.
- `rankOneCocharacterSet_subset` and
  `rankOneCocharacterSet_eq_of_pairing_zero_iff`: the index sets of `ζ`
  and `ζ'` agree. The Levi roots agree. A root `β` positive for `ζ` is
  positive for `ζ'`, or `-β` is; `-β` is a relative root by the
  published `relativeRootNegation`. The annihilators of `β` and `-β`
  together with the Levi roots coincide.
- `rankOneGamma_eq_of_pairing_zero_iff`: for `β` positive for `ζ`, the
  constants of `ζ'` and `ζ` at `N = X_*(A_β)` agree. With
  `a = ⟨β, ζ⟩ > 0` and `b = ⟨β, ζ'⟩ ≠ 0`, the cocharacter
  `ν = a ζ' - b ζ` lies in `N`, since it pairs to zero with `β` and
  with the Levi roots. The published `rankOneGamma_zsmul` replaces `ζ'`
  by `a ζ' = b ζ + ν`, and `rankOneGamma_add_of_mem` removes `ν`. If
  `b > 0`, `rankOneGamma_zsmul` gives the constant of `ζ`. If `b < 0`,
  then `b ζ = (-b)(-ζ)`, and `rankOneGamma_zsmul` with
  `rankOneGamma_neg` gives it.
- `rankOneGammaProduct_eq_of_pairing_zero_iff`: the two rank-one
  products agree, by the equality of index sets and of the factors
  (`finprod_mem_congr`).

In the source's notation, `N` plays the role of `X_*(A_α)` and `M_N` that
of `M_α`. The proof shows that on `M_N` the cocharacter `ζ'` cuts out the
same parabolic and opposite-radical intersections as `ζ` when `b > 0`,
and as `-ζ` when `b < 0`.
