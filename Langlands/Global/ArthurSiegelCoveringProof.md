# Siegel covering for every compact Iwasawa subgroup

Module `Langlands.Global.ArthurSiegelCoveringProof`, namespace
`Langlands.Global.ArthurTruncation`. The theorem `iwasawaSiegelCovering` proves
`IwasawaSiegelCoveringStatement` (module `Langlands.Global.ArthurSiegelSetsIwasawaStatement`):
for every number field `F`, connected reductive `G` (affine, locally of finite type), maximal
split torus `i : T → G`, generic cocharacter `ν`, every compact subgroup `K` with
`P_0(𝔸)K = G(𝔸)` (`IsIwasawaCompact (Standard.parabolicHom i ν ∅) K`) and every `hρ`, there
are compact factor data `C` with `C.compactSubgroup = K` and `T_1 ∈ 𝔞_0` such that
`IsSiegelCovering hG hi hK hρ C T_1`: `G(𝔸) = P_1(F) S^{P_1}(T_1, ω)` for every standard
`P_1`, with one pair `(ω, T_1)` for all `P_1`. This is the choice of `ω` and `T_0` of Arthur,
*A trace formula for reductive groups I* (1978), §6, p.941, and, for `P_1 = G`, the covering of
Arthur, *An introduction to the trace formula* (2005), Theorem 8.1, here for every compact `K`
of the class and not only for Arthur's admissible `K`.

## Auxiliary results

- `positiveTorusMap_apply`: `positiveTorusMap F i a` is the adelic map of `i` applied to the
  underlying torus point of `a`.
- `realParameterPairing_realCharacterDualMap`: for `f : P → Q`, pairing `m ∈ X(Q) ⊗ ℝ` with the
  image of `H` under `realCharacterDualMap f` equals pairing the restriction of `m` along `f`
  with `H` (induction on tensors).
- `eval_height_positiveTorusMap`: for a positive torus point `a` and a character `β` of `T`,
  `β(H_0(a)) = log |β(a)|`, where `H_0 = height hi hK hρ` and
  `|β(a)| = PositiveRealTorus.normCharacter F T β a`. *Proof.* Choose `m` with
  `restrictToTorus F i ν ∅ m = 1 ⊗ β` (`hρ` is surjective). By `eval_eq_pair` and `pair_toA0`,
  `β(H_0(a))` is the pairing of `m` with `H_{P_0}(a)`. As `a` lies in `P_0(𝔸)` through
  `torusToParabolic`, `IsIwasawaCompact.height_map` and `characterLog_map` identify
  `H_{P_0}(a)` with the image of the logarithmic functional of `a` on `T`; the previous item
  turns the pairing into `log |β(a)|`. No property of `K` beyond `hK` enters.
- `rational_mem_parabolicRationalImage`: a rational point of `G` that factors through
  `Standard.parabolicHom i ν S` maps into `P(F) = parabolicRationalImage`
  (`rational_naturality`).

## Proof of `iwasawaSiegelCovering`

1. *Setup and compact factors.* `exists_siegelAlgebraicSetup_of_generic` gives an actual Siegel setup for
   the given `i` and `ν`. The published `exists_unipotentCompactCover_of_setup` gives a compact
   `Ω_N ⊆ N_0(𝔸)` meeting every coset `N_0(F) n`, and `exists_leviCompactCover_of_setup` with
   the proof `centralSplitCompactQuotient` (Springer's compactness theorem) gives a compact
   `Ω_M ⊆ M_0(𝔸)¹` meeting every coset `M_0(F) m`. The compact factor data are
   `C = (Ω_N, Ω_M, K)`, so `C.compactSubgroup = K` holds by definition.
2. *Thresholds.* For each `S₁` in the powerset of `Δ_0`, `exists_relativeChamberReduction`
   (module `Langlands.Global.ArthurSiegelRelativeChamber`) gives `t_{S₁} : ℝ≥0ˣ`. The finitely
   many thresholds have a lower bound `t₀`. Put `c = min(log t₀, 0) − 1` and
   `T_1 = c ⊗ ν ∈ 𝔞_0`. For a simple root `β`, `⟨β, ν⟩` is a positive integer (the definition
   of `positiveRelativeRoots`), so `β(T_1) = c ⟨β, ν⟩ ≤ c < log t₀`.
3. *Covering.* Let `S₁ ∈ (simpleFinset ν hG hi).powerset` and `x ∈ G(𝔸)`. The relative chamber
   reduction gives `q ∈ P_1(F)` and `q x = ι_N(n) ι_M(m) a k` with `m ∈ M_0(𝔸)¹`, `a` a positive
   point of `T` with `t_{S₁} ≤ |α(a)|` for `α ∈ S₁`, and `k ∈ K`. Choose `μ ∈ M_0(F)` with
   `μ m ∈ Ω_M`; then `μ ι_N(n) μ⁻¹ = ι_N(n₂)` for some `n₂ ∈ N_0(𝔸)`, because `P_0(𝔸)`
   normalizes `N_0(𝔸)` (`standardParabolicImage_le_normalizer`). Choose `ρ ∈ N_0(F)` with
   `ρ n₂ ∈ Ω_N`. With `γ = ρ μ q` (images in `G(F)`),
   `γ x = ι_N(ρ n₂) ι_M(μ m) a k`, a group computation as in the published
   `exists_isSiegelCover_of_chamber`.
4. *`γ ∈ P_1(F)`.* The images of `ρ` and `μ` lie in `N_0 ⊆ P_0` and `M_0 ⊆ P_0`
   (`standardUnipotent_le_standardParabolic`, `standardLevi_le_standardParabolic`), and
   `P_0 ⊆ P_1` by `standardParabolicOrder`; with `q ∈ P_1(F)` this gives `γ ∈ P_1(F)` by
   `rational_mem_parabolicRationalImage`.
5. *Chamber.* For `β ∈ S₁`, `eval_height_positiveTorusMap` gives
   `β(H_0(a) − T_1) = log |β(a)| − β(T_1) ≥ log t₀ − β(T_1) > 0`, using
   `t₀ ≤ t_{S₁} ≤ |β(a)|`. Hence `γ x ∈ S^{P_1}(T_1, ω)` (`mem_siegelSet_iff`), and
   `x = γ⁻¹ (γ x) ∈ P_1(F) S^{P_1}(T_1, ω)`.

## Inputs and provenance

The proof uses no hypothesis beyond those of the statement. Besides the module
`Langlands.Global.ArthurSiegelRelativeChamber`, it uses the published proofs
`centralSplitCompactQuotient`, `rankOneParabolicRationalOrbitHeightBound` (through the relative
reduction), `genericMinimalParabolic`, `derivedMaximalSplitTorus`,
`derivedCentralSplitTorusProduct` and `standardParabolicOrder`, and the published lemmas named
above. The comparison `hρ` is used only to read heights in `𝔞_0`; `K` enters only through its
compactness (the distortion constant of the relative reduction) and `P_0(𝔸)K = G(𝔸)` (the
Iwasawa factorization). The constants `ω`, `T_1` depend on `K`, as the statement allows.

The route is not Arthur's: Arthur obtains the covering "by the properties of Siegel sets" for
his admissible `K` (1978, p.941), and Arthur 2005, Theorem 8.1, cites Borel and Harish-Chandra.
Here the covering for every `P_1` is proved directly by height minimization over `P_1(F)` (the
relative chamber reduction), so no reduction theory of the Levi subgroups `M_1` and no transfer
between compact subgroups is needed.
