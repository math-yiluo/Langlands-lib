# Finiteness of `γ(M_α|M)` and of `c(G|M)`

Worker 5. This module proves that the rank-one constants `γ(M_α|M)` in
Waldspurger's constant

`c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)`

are finite. It follows that `c(G|M)` is a positive real number. The source
is J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), I.1, printed
pp.240-241 / PDF pp.6-7. There `γ(P) = ∫_Ū δ_P(m_P(ū)) dū` is defined in
formula (2) as a real number, `γ(G|M) = γ(P)`, and `c(G|M)` is defined on
p.241 from the constants `γ(M_α|M)` of the Levi subgroups
`M_α = Z_G(A_α)`. Waldspurger treats these constants as finite positive
numbers without a separate statement. This module proves that finiteness
for the Lean objects of the module `RationalPlancherelConstant`.

The results are derived. The proofs follow a standard route that is not
taken from Waldspurger's text. `M_α` is the centralizer of one generic
cocharacter, so it is the group of points of a smooth closed subgroup
scheme. Then `γ(M_α|M)` equals the Library's constant `γ` of that group
scheme, and the Library proves that `γ` is finite for smooth groups.

## Setting

The objects `cocharacterSubmoduleCentralizer`, `leviGamma`,
`rankOneGamma`, `rankOneGammaProduct`, `plancherelConstant` and
`plancherelConstantReal` are those of
`Langlands.Representation.Plancherel.RationalPlancherelConstant`. In
particular, for an integer submodule `N` of the cocharacter lattice
`X_*(T)`, `cocharacterSubmoduleCentralizer i N` is the intersection of the
dynamic centralizers `Z_G(ν ≫ i)`, `ν ∈ N`. For `N = X_*(A_α)` this is
`M_α`. `rankOneGamma i ζ K hK N` is the common-compact open-cell constant
of `P ∩ M_N(F)` and `Ū ∩ M_N(F)` computed in `G(F)`, with
`P = P_G(ζ ≫ i)` and `Ū = U_G((ζ ≫ i)⁻¹)`. All Haar measures give mass
`1` to the intersection with the fixed compact open subgroup `K`.

The main results assume that `F` is a nonarchimedean local field, that
`G` is an affine group scheme over `F` that is smooth and has connected
underlying scheme, and that `i : T → G` is a homomorphism from a split
torus (`IsSplitTorus T.toGrp`). In the intended application `T` is a
maximal split torus. Reductivity is not needed.

## Common-compact constants along closed embeddings

This section is pure topological group theory. `A` and `B` are
topological groups, `emb : B →* A` is a homomorphism, and `K` is a compact
open subgroup of `A`.

- `subgroupEmbeddingEquiv emb hemb P P' hpar hrange`: if `emb` is an
  embedding, `P ≤ B`, `P' ≤ A`, `emb b ∈ P' ↔ b ∈ P` for all `b`, and
  every element of `P'` lies in the image of `emb`, then `emb` restricts
  to an isomorphism of topological groups `P ≃ₜ* P'`.
  `subgroupEmbeddingEquiv_apply_coe` records that it is `emb` on
  elements.
- `measurePreserving_subgroupEmbeddingEquiv`: if moreover `emb` is a
  closed embedding, `A` is locally compact, and `P`, `P'` are closed, then
  this isomorphism carries the Library's `subgroupCompactOpenHaar` of `P`
  for the compact open `emb⁻¹(K)` of `B` to that of `P'` for `K`. There is
  no scalar factor. The image measure is a regular Haar measure on `P'`.
  It gives mass `1` to `P' ∩ K`, because the preimage of `P' ∩ K` is
  `P ∩ emb⁻¹(K)`, which has mass `1`. The Library's uniqueness statement
  `compactOpenHaarAlong_eq_of_mass_one` then identifies the two measures.
- `compactNormalizedSourceGamma_eq_of_isClosedEmbedding`: under the same
  hypotheses for two pairs `(P, P')` and `(V, V')`, the Library's
  `compactNormalizedSourceGamma` of `P'`, `V'` in `A` for `K` equals that
  of `P`, `V` in `B` for `emb⁻¹(K)`. The proof changes variables in both
  integrals by the two measure-preserving isomorphisms. It then uses
  `emb(p) emb(v)⁻¹ = emb(p v⁻¹)`, which lies in `K` exactly when
  `p v⁻¹ ∈ emb⁻¹(K)`.

## A generic cocharacter of a submodule (any field `k`)

- `exists_mem_forall_latticePairing_ne_zero`: let `s` be a finite set of
  characters of `T`, each with nonzero pairing against some element of a
  submodule `N` of `X_*(T)`. Then one element `ν ∈ N` has nonzero pairing
  with every character in `s`. The proof is by induction on `s`. Given `ν`
  for `s` and `ξ ∈ N` with `⟨a, ξ⟩ ≠ 0` for the new character `a`, take
  `ν + m ξ` with `m = 1 + Σ_{c ∈ s ∪ {a}} |⟨c, ν⟩|`. If `⟨b, ξ⟩ = 0`, the
  pairing with `b` is `⟨b, ν⟩`, and `b ≠ a`. Otherwise it vanishes only if
  `|⟨b, ν⟩| = m |⟨b, ξ⟩| ≥ m`, which contradicts `|⟨b, ν⟩| < m`.
- `IsGenericInSubmodule i N ν` means that `ν ∈ N` and every relative root
  of `i` (an element of the Library's `relativeRoots i`) that vanishes at
  `ν` vanishes on all of `N`.
- `exists_isGenericInSubmodule`: if `relativeRoots i` is finite, every
  submodule has a generic element. Apply the previous lemma to the roots
  that do not vanish on `N`.

This extends the Library's `IsSplitTorus.exists_pairings_ne_zero`, which
treats the whole lattice, to an arbitrary submodule.

## `M_N` is the centralizer of one cocharacter

The section assumes `G` affine and locally of finite type over a field
`k`, and `T` split.

- `weightSpace_zero_le_of_pairing`: if every relative root vanishing at
  `ν` also vanishes at `ξ`, then the zero weight space of `ν ≫ i` on the
  Lie algebra is contained in that of `ξ ≫ i`. The proof writes the zero
  weight space of `ν ≫ i` as the sum of the weight spaces of `T` for the
  characters `a` with `⟨a, ν⟩ = 0`, using the Library's
  `weightSpace_comp_eq_iSup`. Each such summand is either zero, or has
  `a = 0`, or has `a` a relative root. In the last case `⟨a, ξ⟩ = 0` by
  hypothesis. In each case the summand lies in the zero weight space of
  `ξ ≫ i` by `weightSpace_le_comp`.
- `dynamicCentralizer_le_of_pairing`: if moreover `G` is smooth with
  connected underlying scheme, then `Z_G(ν ≫ i) ≤ Z_G(ξ ≫ i)`. This
  applies the Library's `dynamicCentralizer_le_of_weightSpace_zero_le`
  (with the Library's `dynamicSmooth`, `dynamicConnected`, `dynamicLie`
  and `lieSubgroupEquality`). Its other hypothesis is that the image of
  `ν ≫ i` lies in `Z_G(ξ ≫ i)`. This holds because the image of `i` lies
  in the centralizer of `T` (`range_le_torusCentralizer`), which lies in
  `Z_G(ξ ≫ i)` (`torusCentralizer_le_dynamicCentralizer`).
- `dynamicCentralizer_eq_cocharacterSubmoduleCentralizer`: for `ν` generic
  in `N`, `Z_G(ν ≫ i) = cocharacterSubmoduleCentralizer i N`.
- `exists_dynamicCentralizer_eq_cocharacterSubmoduleCentralizer`: for
  every submodule `N` such a `ν ∈ N` exists. Finiteness of the relative
  roots is the Library's `IsSplitTorus.finite_relativeRoots`.

For `N = X_*(A_α)` this proves `M_α = Z_G(ν)` for a cocharacter `ν` of
`A_α` in general position.

## Closed subgroup schemes on rational points

`F` is a nonarchimedean local field. `G` and `H` are affine group schemes
over `F`, locally of finite type. `S` is a subgroup functor of `G`
represented by a closed subgroup scheme `j : H → G` (hypotheses
`hj : S.IsRepresentedBy j` and `hjc : IsClosedSubgroup j`). The point
topologies are those of `RationalPlancherelConstant`.

- `closedSubgroupPointHom hj hjc : H(F) →* G(F)` is `x ↦ x ≫ j`, built
  from the Library's `rationalPointSubgroupHomeomorph`.
  `isClosedEmbedding_closedSubgroupPointHom` proves that it is a closed
  embedding, by the Library's `isClosedEmbedding_rationalPointMap`. Its
  image is `S(F)` (`closedSubgroupPointHom_mem`,
  `exists_closedSubgroupPointHom_eq`).
- `closedSubgroupCompact hj hjc K` is the compact open subgroup of `H(F)`
  that is the preimage of `K`. `isCompact_closedSubgroupCompact` proves
  that it is compact.
- `leviGamma_eq_gamma_of_isClosedSubgroup`: let `χ'` be a cocharacter of
  `H` with `χ' ≫ j = χ`. Then the constant `leviGamma χ K hK (S(F)) hS` of
  the closed subgroup `S(F)` of `G(F)` equals the Library's
  `gamma χ' (closedSubgroupCompact hj hjc K) _` of `P_H(χ')` in `H`. The
  proof uses the Library's `Dynamic.parabolic_eq_comap_of_isClosedSubgroup`
  and `Dynamic.unipotent_eq_comap_of_isClosedSubgroup`. They identify the
  preimages of `P_G(χ) ∩ S(F)` and `U_G(χ⁻¹) ∩ S(F)` with `P_H(χ')(F)`
  and `U_H(χ'⁻¹)(F)`. The transport theorem of the previous section then
  applies.
- `leviGamma_ne_top_of_isClosedSubgroup`: if `H` is smooth, this constant
  is finite, by the Library's `gamma_ne_zero_ne_top_of_smooth`.

## Finiteness of `γ(M_α|M)` and `c(G|M)`

Here `G` is smooth with connected underlying scheme, and `T` is split.

- `rankOneGamma_ne_top`: for every submodule `N`,
  `rankOneGamma i ζ K hK N ≠ ⊤`. Choose `ν` as above with
  `M_N = Z_G(ψ)`, `ψ = ν ≫ i`. The Library's affine centralizer scheme
  `Dynamic.Affine.centralizerScheme ψ` represents `Z_G(ψ)` as a closed
  subgroup scheme (`Dynamic.Affine.isRepresentedBy_centralizerHom`,
  `Dynamic.Affine.isClosedSubgroup_centralizerHom`). It is smooth by
  `Dynamic.smooth_affineCentralizer_overRing`. Since `T` is commutative,
  `ζ ≫ i` factors through it, by `Dynamic.intersectionCocharacter` and
  `Dynamic.intersectionCocharacter_comp`. The previous section then gives
  finiteness.
- `rankOneGammaProduct_ne_top_of_isSplitTorus`: the product
  `∏ γ(M_α|M)` is finite.
- `plancherelConstant_ne_top_of_isSplitTorus`: `c(G|M) ≠ ⊤`.
- `plancherelConstant_pos_ne_top`: `0 < c(G|M)` and `c(G|M) ≠ ⊤`, as an
  element of `ℝ≥0∞`. Positivity is the existing
  `plancherelConstant_ne_zero_of_smooth`.
- `plancherelConstantReal_pos_of_isSplitTorus`: the real value
  `plancherelConstantReal i ζ K hK` is positive.

These results discharge the finiteness hypothesis on every rank-one
factor in `plancherelConstant_ne_top` and
`plancherelConstantReal_pos_of_smooth` of `RationalPlancherelConstant`
when `T` is split and `G` is smooth and connected.

## Not proved here

- The identification of `rankOneCocharacterSet`, the submodule
  centralizers and `rankOneGamma` with Waldspurger's `Σ_red(P)`, `M_α`
  and `γ(M_α|M)`. This module proves that `M_N` is a centralizer of one
  cocharacter, so it is a smooth closed subgroup scheme. It does not prove
  that `M_N` is reductive or a Levi subgroup.
- Remark (3) of I.1 (independence of the parabolic `P` with Levi `M`, for
  the fixed compact `K`), and any comparison for different compact open
  subgroups `K`.
- The density `μ(ω)` and any Plancherel identity.
