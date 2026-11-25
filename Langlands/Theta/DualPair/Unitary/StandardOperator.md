# The Leray splitting of `U(ν, ν)` through the standard Weil operator

**GKT Proposition 12.27 (1)** (p. 372) and **Proposition 12.29** (p. 375) in Case `3₊` with `W`
split, expressed through the standard Weil operator `r` of GKT §2.3 (Definition 2.9, p. 54;
Lemma 2.16, p. 58; (2.24), p. 64), with the Rao function on the Siegel parabolic (GKT Corollary
4.36, Definition 4.37: `x(p₁ w p₂) = det(p₁ p₂|_X)`).

The module `Langlands.Theta.DualPair.Unitary.StandardOperator` shows that the Library's Weil
representation `lerayWeil c ν ψ χ Q` of `U(ν, ν)` (module `Langlands.Theta.DualPair.Unitary.LeraySplitting`) is `β(g) · r(g ⊗ 1)` on the Siegel
parabolic and at the Weyl element, with `r` the general standard operator of
`Langlands.Theta.Metaplectic.StandardOperator` for the book's form `⟪,⟫ = polarizedForm
(hermitianTracePairing c Q)` on `𝕎 = 𝕏^* × 𝕏`, `𝕏^* = 𝕏 = M_{α×ν}(E)`. This decides which of `χ`
and `χ⁻¹` is the book's character, and the sign of the kernel at the Weyl element.

## Content

`U(ν, ν)` acts on `𝕎` through `UnitaryGroup.toTraceIsometry` (`g` acts by `w ↦ w g⁻¹` on
`M_{α×2ν}(E)`), and `ψ` is the book's character (`UnitaryAdditiveCharacter`).

**Matrices and the parabolic.**

- `toCols₁_fromCols_mul`, `toCols₂_fromCols_mul`, `toTraceIsometry_apply_eq`,
  `isometryInv_toTraceIsometry`: the action in blocks.
- `toTraceIsometry_mem_siegelParabolicGroup`: the Siegel parabolic of `U(ν, ν)` goes into the
  Siegel parabolic of `𝕏 = 0 × M_{α×ν}(E)` (the book's `P(X) ⊗ 1 ⊆ P(𝕏)`).
- `standardD_toTraceIsometry`, `standardB_toTraceIsometry`: for `mat p = [[A, B], [0, D]]`, the
  blocks of `ι(p)⁻¹` on `𝕏^*` are `d x = x A` and `b x = x B`.
- `toBlocks₂₂_mat_inv_of_mem`: `(p⁻¹)₂₂ = c(A)ᵀ` (from `p⁻¹ = −H c(p)ᵀ H`); `det_toBlocks₁₁_ne_zero`.
- `siegelParabolicRaoValue hp`: **the Rao value `x(p) = det_E(p|_X)`**, the determinant of the
  action `v ↦ v (p⁻¹)₂₂` of `p` on the Lagrangian `X = {(0, v)}` of `W = E^{2ν}`;
  `siegelParabolicRaoValue_eq`: `x(p) = c(det A)`.
- `isPerfPair_hermitianTracePairing`: `⟪,⟫` is perfect (for invertible Hermitian `Q`).

**The two decisions.** The theorems below take as instance hypotheses the module topology and the
topological group structure of `M_{α×ν}(E)` (given by `isModuleTopology_matrix`), a Borel σ-algebra,
and the perfectness of `⟪,⟫` (given by `isPerfPair_hermitianTracePairing`).

- `standardOperator_toTraceIsometry_of_mem_siegelParabolic`: **Lemma 2.16 for the pair**,
  `r(p ⊗ 1) φ(x) = |N det A|^{|α|/2} ψ(½ ⟪x A, x B⟫) φ(x A)` (`|det_F(x ↦ x A)| = |N det A|^{|α|}`,
  `det_restrictScalars_mul_mul`).
- `lerayWeil_eq_smul_standardOperator_of_mem_siegelParabolic`: `lerayWeil p = χ(det A) · r(p ⊗ 1)`.
- `lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic`: **`lerayWeil p =
  χ(x(p))⁻¹ · r(p ⊗ 1)`**. In the book's normalization `β(m(a)) = χ^{book}(det a)` (Proposition
  12.29, `det a = x(m(a))`), so **`χ^{book} = χ⁻¹`**: the Library's `χ(det A)` is
  `χ^{book}(c(det A))`. (`χ(c z) = χ(z)⁻¹` by (11.2), `IsQuadraticInvolution.map_map_eq_inv`.)
- `toTraceIsometry_weylElement`: **the Library's `weylElement c ν = [[0, 1], [−1, 0]]` is the Weyl
  element `w_J` with `J = −1`** (`(x, y) ↦ (y, −x)` on `𝕏^* × 𝕏`), the book's `w_{n/2}` for the
  standard basis `e_i = (0, ε_i)`, `e^*_i = J e_i = −(ε_i, 0)`.
- `standardOperator_weylElement`: from the general definition, **`r(w ⊗ 1) φ(x) = ∫ ψ(⟪x, y⟫) φ(y)
  dy`** for the self-dual measure of `ψ ∘ ⟪,⟫`: the kernel is `ψ(+⟪x, y⟫)` (GKT (2.24) with
  `I = J⁻¹ = −1`, `ψ̄(⟨z, I y⟩) = ψ(⟪y, z⟫)`); `hermitianTracePairing_neg_symm`.
- `lerayWeil_weylElement_eq_smul_standardOperator`: **`lerayWeil w = β(w) · r(w ⊗ 1)`** with
  `β(w) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}` (`lerayScalar_selfDualMeasure` of `Langlands.Theta.DualPair.Unitary.LerayScalar`), Proposition
  12.27 (1) verbatim at `w`.

So `IsLerayWeil` is Proposition 12.27 (1) for the book's splitting `s^V_{ψ, χ⁻¹}` on the
generators `P` and `w` of `U(ν, ν)`.

## Declarations

- `toCols₁_fromCols_mul`, `toCols₂_fromCols_mul`, `toTraceIsometry_apply_eq`,
  `isometryInv_toTraceIsometry`, `toTraceIsometry_mem_siegelParabolicGroup`,
  `standardD_toTraceIsometry`, `standardB_toTraceIsometry`, `toBlocks₂₂_mat_inv_of_mem`,
  `det_toBlocks₁₁_ne_zero`, `siegelParabolicRaoValue`, `siegelParabolicRaoValue_eq`,
  `toTraceIsometry_weylElement`.
- `isPerfPair_hermitianTracePairing`, `standardOperator_toTraceIsometry_of_mem_siegelParabolic`,
  `lerayWeil_eq_smul_standardOperator_of_mem_siegelParabolic`,
  `lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic`,
  `hermitianTracePairing_neg_symm`, `standardOperator_weylElement`,
  `lerayWeil_weylElement_eq_smul_standardOperator`.

All in the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.DualPair.Unitary.LerayScalar` (`lerayWeil`, its formulas, `lerayScalar_selfDualMeasure`),
`Langlands.Theta.Metaplectic.WeylElement` (and through it `StandardOperator`, `SiegelParabolic`).
