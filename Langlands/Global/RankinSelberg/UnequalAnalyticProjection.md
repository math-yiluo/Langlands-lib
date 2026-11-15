# The padded projection of an automorphic function

Provenance: internal. This module supports the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
Cogdell's integral involves the projection `P^(r+1)_(m+1) φ` of a cusp form `φ` on
`GL_(r+1)` and evaluates it at `diag(g, 1)` for `g ∈ GL_m(𝔸)`. The Library definition
`projection` (module `Langlands.Global.RankinSelberg.UnequalIntegrals`) extends it to all of
`GL_(m+1)(𝔸)`:
`projection F h ψ φ p = detPower p (-(r - m)/2) · subgroupCharacterCoefficient … φ (pad p)`.
The coefficient is
`∫_{Y(F) \ Y(𝔸)} φ(y x) conj ψ_Y(y) dy` along the radical `Y = Y_(r+1,m)`
(`projectionUnipotent F (r + 1) m`, block type `(m + 1, 1, …, 1)`). The character is
`ψ_Y(y) = ψ(∑ y_(i,i+1))` (`projectionCharacter`), and the measure is the normalized quotient
measure `normalizedRationalQuotientHaarMeasure`. This module proves that
`g ↦ P φ (diag(g, 1))` is continuous, left `GL_m(F)`-invariant and rapidly decreasing in
`|log |det g||`. These facts, with the integrability of the cusp form `φ'`, give the
convergence and the functional equation of the global integral.

Throughout, `φ : Points F (r + 1) → ℂ` is a function on the actual adelic points, and the
hypotheses used are:

- `Continuous φ`;
- left invariance under rational points:
  `φ (AdelicGroupPoints.rational F _ c * x) = φ x`;
- `HasBasisDecay F (r + 1) φ` (defined here): for every `N ≥ 0` there is `C` with
  `‖φ x‖ ≤ C exp (-N |log |det x||)` whenever the matrix of `x` has some column and some row
  equal to a standard basis vector. For cusp forms this is the theorem
  `exists_norm_le_of_basis_column_row` of `UnequalAnalyticDecay`;
- `ψ` continuous, trivial on `F`, of norm one.

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`.

## Generic facts

- `inv_measure_univ_smul_univ_le_one`: `(ν univ)⁻¹ • ν` has total mass at most `1`. This
  holds also when `ν univ` is `0` or `∞`. So the coefficient is bounded by the supremum of the
  integrand without using compactness of `Y(F) \ Y(𝔸)`.
- `lift_eq_out`: on `LeftCosetSpace Γ`, the descended function at a class `q` is the function at
  the representative `Quotient.out q`.
- `subgroupConj S D hD`: conjugation `y ↦ D⁻¹ y D` as a topological group automorphism of a
  subgroup `S` normalized by `D` (`hD : D⁻¹ y D ∈ S ↔ y ∈ S`); `coe_subgroupConj_apply`.
- `conj_mem_blockUnipotent_iff`: for `P` in the block parabolic,
  `P⁻¹ y P ∈ Y ↔ y ∈ Y` (`radical_conj` applied to `P` and `P⁻¹`).

## The radical and its character

- `radical F r m` and `radicalRational F r m`: abbreviations for `Y(𝔸)` and `Y(F) ⊆ Y(𝔸)`.
  `LocallyCompactSpace` comes from closedness (Library instance
  `projectionUnipotentClosed`).
- `mem_radical_iff`, `mem_rationalPoints_iff`, `mem_radicalRational_iff`: membership in
  terms of the matrices (Library `mem_blockUnipotent_affinePoints_iff`).
- `detNorm_radical`: elements of `Y(𝔸)` have `|det| = 1` (`radical_det`).
- `projectionCharacter_mul` (from `radical_superdiag_mul`), `projectionCharacter_rational`:
  `ψ_Y` is trivial on `Y(F)`, since the superdiagonal sum of a rational point is the image of
  an element of `F`. Also `norm_projectionCharacter`, `continuous_projectionCharacter`, and
  `projectionCharacter_conj`: `ψ_Y` is unchanged by a conjugation fixing the superdiagonal.

## The coefficient

- `coeffKernel F ψ φ x y = φ(y x) conj ψ_Y(y)`. `coeffKernel_rational_mul`: it is left
  invariant under `Y(F)`, by the invariance of `φ` and the triviality of `ψ_Y` on `Y(F)`.
  `continuous_coeffKernel`.
- `coeff_eq`: the Library coefficient equals the integral over `Y(F) \ Y(𝔸)` of the descended
  kernel (`lift_eq_out`).
- `normalizedMeasure_univ_le_one`; instance `normalizedMeasure_isFiniteMeasure`.
- `norm_coeff_le`: if `‖φ(y x)‖ ≤ M` for all `y ∈ Y(𝔸)` and `M ≥ 0`, then
  `‖coefficient at x‖ ≤ M` (`norm_integral_le_of_norm_le_const`, mass `≤ 1`).
- `continuous_coeff_comp`: for a continuous family `a ↦ f a` with a uniform bound
  `‖φ(y f a)‖ ≤ M`, the coefficient at `f a` is continuous in `a`. This is
  `continuous_of_dominated` with a constant bound; measurability of the integrand on the
  quotient comes from continuity of the descended kernel and the Library Borel structure
  `rationalQuotientBorelSpace`.
- `coeff_rational_mul` (**invariance under rational conjugation**): let `D` be a rational
  point whose matrix lies in the parabolic over `F` and over `𝔸` and whose conjugation fixes
  the superdiagonal of `Y`. Then the coefficient at `D x` equals the coefficient at `x`.
  Proof: `α = subgroupConj (radical) D` maps `Y(F)` onto itself, because `D` is rational
  and normalizes `Y` over `F`. The kernel at `D x` is the kernel at `x` composed with `α`:
  `φ(y D x) = φ(D⁻¹ y D x)` by the invariance of `φ`, and `ψ_Y(α y) = ψ_Y(y)`. The induced map of
  `Y(F) \ Y(𝔸)` scales the quotient measure by `(mulEquivHaarChar α)⁻¹`
  (`map_haar_eq_smul`, `map_cosetMap_discreteQuotientMeasure` from
  `UnequalAnalyticQuotientMeasure`). It therefore preserves the normalized measure
  (`map_inv_measure_univ_smul`), and `MeasurePreserving.integral_comp'` concludes.

## The padded projection

- `projection_pad_eq`:
  `P φ (diag(g, 1)) = detPower g (-(r - m)/2) · (coefficient at diag(g, I))`, by
  `detPower_pad` and `pad_pad`.
- `exists_norm_radical_mul_pad_le`: for `y ∈ Y(𝔸)` and `g ∈ GL_m(𝔸)`, the matrix
  `y diag(g, I)` has column `m` equal to `e_m` (`radical_col`, `padGL_col`,
  `mul_apply_of_col`), last row equal to the last basis row (`radical_row`, `padGL_row`,
  `mul_apply_of_row`), and `|det| = |det g|`. Hence
  `‖φ(y diag(g, I))‖ ≤ C exp (-N |log |det g||)` with `C ≥ 0`, uniformly in `y`.
- `continuous_projection_pad`: `g ↦ P φ (diag(g, 1))` is continuous. Use
  `continuous_coeff_comp` with the bound for `N = 0`, and `continuous_detPower`.
- `projection_pad_rational_mul`: it is left invariant under `GL_m(F)`. Here
  `diag(c g, I) = diag(c, I) diag(g, I)` and `diag(c, I)` is rational (`pad_rational`). Its
  matrix lies in the parabolic (`padGL_mem_parabolic`) and fixes the superdiagonal
  (`radical_superdiag_conj`), so `coeff_rational_mul` applies. Also `detPower` is invariant by
  the product formula.
- `exists_norm_projection_pad_le`: for every `N ≥ 0` there is `C ≥ 0` with
  `‖P φ (diag(g, 1))‖ ≤ C exp (-N |log |det g||)`. Take the bound of
  `exists_norm_radical_mul_pad_le` with `N + (r - m)/2`. This absorbs the factor
  `|detPower g (-(r - m)/2)| = exp (-(r - m)/2 · log |det g|) ≤ exp ((r - m)/2 · |log |det g||)`.
