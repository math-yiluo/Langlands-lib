# Auxiliary lemmas for V 6 at Galois-fixed points

Authors: Worker 91 (Lean proofs and Markdown); Worker 47 (rechecked against the published
Library and submitted).

Lean module: `Langlands.Geometry.Building.UnramifiedFixedCentralizerAux`.

This module collects general lemmas used by
`Langlands.Geometry.Building.UnramifiedFixedCentralizerReduction`. That module proves that the
Levi transport statement implies V 6 on `Z_G(S)(F)` at the Galois-fixed points. Every lemma
here is an internal consequence of published Library results. None is a statement from the
literature, and none assumes a local field: the lemmas hold over an arbitrary field `k`, or
over an arbitrary base scheme `B`.

## Integral characters with a prescribed restriction (section `Integral`)

- `toRat_injective_of_isSplitTorus`: for a split torus `S`, the map
  `χ ↦ 1 ⊗ χ` from `X^*(S)` to `ℚ ⊗ X^*(S)` is injective. Proof: after the published
  `toReal`, equal images give equal real pairings with every cocharacter. The integral
  pairing of a split torus is perfect (`IsSplitTorus.isPerfPair_latticePairing`), so its
  left kernel is trivial.
- `exists_nsmul_eq_toRat_of_mem_ratSpan`: let `A` be an additive subgroup of an abelian group
  `M`. Every element `x` of the rational span of `A` in `ℚ ⊗ M` satisfies `m • x = 1 ⊗ r` for
  some `m > 0` and `r ∈ A`. Proof: induction on the span, clearing denominators.
- `exists_characterRestriction_eq_nsmul`: let `S` be a split torus and `s : S → Z` a
  homomorphism such that the published restriction evaluation
  `Cartan.restrictionEvaluation s : V(S) → Hom(X^*(Z)_k, ℝ)` is bijective. Then for every
  character `a` of `S` there are a rational character `χ` of `Z` and an `m > 0` with
  `Cartan.characterRestriction s χ = m • a`.

  Proof. Suppose `1 ⊗ a` is not in the real span of the restrictions. A linear form on
  `ℝ ⊗ X^*(S)` then vanishes on the span but not at `1 ⊗ a`
  (`Submodule.exists_dual_map_eq_bot_of_notMem`). The real pairing of a split torus is
  perfect (`isPerfPair_of_isSplitTorus`), so this form is pairing with some `v ∈ V(S)`. The
  restriction evaluation sends `v` to `0`, so `v = 0` by injectivity, a contradiction. Real
  span membership gives rational span membership (`RationalSpan.toReal_mem_span_iff`).
  Clearing denominators and applying the injectivity above gives the claim.

## Translations by powers of a normalizer element (section `Translation`)

Here `i : T → G` is a monomorphism over a field, and `φ` a root-function family.

- `RootFunctionFamily.pow_smul_eq_sum_vadd`: if `w • φ = t + φ` for `w ∈ N_i(k)` and
  `t ∈ V(T)`, then `w ^ N • φ = (∑_{j < N} w ^ j • t) + φ`. Proof: induction on `N`, with
  `RootFunctionFamily.smul_vadd`.
- `weylAction_inv_pow_apply_of_inv_apply`: a character fixed by the Weyl action of `w⁻¹` is
  fixed by that of every `(w ^ j)⁻¹`.
- `natCast_mul_eval_eq_of_pow_smul`: let `φ` be a valuation of the root datum with
  `w • φ = t + φ` and `w ^ N • φ = ν + φ`. Let `ξ` be a character fixed by the Weyl action of
  `w⁻¹` and vanishing on the common kernel `rootAnnihilator i` of the roots. Then
  `N · ξ(t) = ξ(ν)`. Proof: by the previous lemma and
  `IsRootDatumValuation.vadd_eq_vadd_iff`, `ν - ∑_{j<N} w ^ j • t` lies in the root
  annihilator. Apply `ξ`, and note that `ξ(w ^ j • t) = ξ(t)` by `eval_normalizer_smul`.

## Weyl invariance of characters of a subgroup (section `WeylInvariance`)

- `weylAction_torusCharacterRestrict_of_comp`: let `iT = τ ≫ j` with `j : M → G` a
  monomorphism, and let `w ∈ N_{iT}` be the image `m ≫ j` of a point `m` of `M`. Then for
  every rational character `ψ` of `M`, the Weyl action of `w` fixes the restriction of `ψ`
  along `τ`. Proof: `IsNormalizingPoint.of_comp` shows that `m` normalizes `τ` through the
  same automorphism of `T`. Characters are invariant under inner automorphisms
  (`comp_innerIso_hom`).

## Finite order modulo the centralizer (section `Centralizer`)

- `exists_pow_mem_centralizerPoints`: let `i : T → G` be a closed split torus in an affine
  group of finite type over a field. For every `w ∈ N_i(k)`, some positive power `w ^ N`
  centralizes `T`. Proof: the full Weyl image is finite (`splitTorusWeylImageFinite`), so the
  Weyl action of `w` has finite order. On a split torus, a trivial Weyl action means
  centralizing (`IsSplitTorus.weylAction_eq_one_iff`).

## Points of represented centralizers (section `Points`)

- `exists_comp_eq_of_mem_centralizerPoints`: if `j` represents the torus centralizer of `i`,
  every point centralizing `i` is `m ≫ j` for a point `m` of the representative.
- `kernelCentralizer_le_torusCentralizer`: if `f ≫ χ = 0` for `f : S ⟶ T` and a character
  `χ` of `T`, the full kernel centralizer of `χ` (for `iT`) lies in the torus centralizer of
  `f ≫ iT`. Proof: `S` maps into the kernel of `χ`, through the published
  `kernelPointsEquiv`.

## Characters of a centralizer on root groups (section `Unipotent`)

- `exists_latticePairing_pos_of_ne_zero_of_isSplitTorus`: a nonzero character of a split
  torus pairs positively with some cocharacter.
- `exists_map_eq_and_eval_eq_one_of_mem_rootGroupPoints`: let `iT : T → G` with `T` split,
  `f : S ⟶ T`, and `j : M → G` a closed representative of the centralizer of `f ≫ iT`. Let
  `iT = τ ≫ j`, with `M` smooth and affine. Let `χ ≠ 0` be a character of `T` with
  `f ≫ χ = 0`. Then every point `u` of the root group `U_χ` is `j(m)` for a point `m` of `M`
  with `ψ(m) = 1` for the given rational character `ψ` of `M`.

  Proof. `U_χ` centralizes the kernel of `χ` (`RelativeRoot.subgroup_le_kernelCentralizer`),
  hence `S` (previous section), so `u = j(m)`. Choose a cocharacter `λ` of `T` with
  `⟨χ, λ⟩ > 0`. Then `u` lies in the dynamic unipotent subgroup `U_G(λ)`
  (`RelativeRoot.subgroup_le_dynamicUnipotent`). Because `j` is closed, `m` lies in
  `U_M(τ ∘ λ)` (`Dynamic.unipotent_eq_comap_of_isClosedSubgroup`). That subgroup has a
  closed representative (`Dynamic.Affine.unipotentHom`). This representative is unipotent
  because `M` is smooth and affine (`Dynamic.isUnipotent_unipotentRepresentative`). Every
  homomorphism from a unipotent group to `𝔾_m` is trivial
  (`IsUnipotent.hom_eq_zero_of_isSplitTorus`), so `ψ(m) = 1`.
- `exists_map_eq_and_eval_eq_one_of_mem_iSup`: the same conclusion for every element of the
  subgroup generated by subgroups `A χ ≤ U_χ`, over the roots `χ` of `T` with `f ≫ χ = 0`.
  The images under `j` of the points killed by `ψ` form a subgroup containing each
  generator.
