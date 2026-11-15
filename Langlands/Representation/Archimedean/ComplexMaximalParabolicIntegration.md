# The `U(n)`-integral in coordinates of the maximal parabolic subgroup `P_{n-1,1}` of `GL_n(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of Worker 5220's module
`MaximalParabolicIntegration` for `GL_n(ℝ)` (candidate `b853be2a`, Task 6749), and follows its proof
step by step.

The module writes the integral over `U(m+1)` of a function in the principal series of the modulus
character `δ_B` as an integral over the opposite unipotent radical of the maximal parabolic
subgroup `P_{m,1}`, followed by an integral over the Levi compact `U(m)`. The statement is
`Langlands.Archimedean.ComplexMaximalParabolicIntegrationStatement`, proved as
`Langlands.Archimedean.complexMaximalParabolicIntegration`. In the proof of
`ComplexStandardLanglandsQuotientStatement` this formula turns the integration pairing over
`U(n)` into an iterated integral, to which the partial Jacquet integral over `P_{n-1,1}` and its
limit argument are applied.

Notation: `U(n)` is the subgroup `unitaryCompact ℂ n` of `Langlands.GeneralLinear n ℂ`, with the
Library's Haar probability measure `ComplexDuality.unitaryHaar n`. Row vectors are `Fin m → ℂ`
with Lebesgue measure. `Fin.snoc v 1` is the row vector `(v, 1)`, and `Fin.last m` is the last
index of `Fin (m+1)`. `ComplexKIntegralInvariance.modulusCharacter n` is the list of characters
`z ↦ (|z|²)^((n-1)/2 - i)`; a function lies in `principalSeries ℂ n (modulusCharacter n)` exactly
when it is smooth and `F(diag(a) u g) = ∏ᵢ |aᵢ|^{2(n-1-2i)} F(g)` for upper unipotent `u`, i.e. it
lies in the principal series of `δ_B`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.ComplexMaximalParabolicIntegration`; `sqNorm`, `lastRow`, `chartWeight`,
`gaussian`, `gaussianMoment`, `exists_unitary_lastRow` and `integral_lastRow` are from
`ComplexLastRowIntegral`, and `integral_mul_eq` from `ComplexKIntegralInvariance`.

## The statement

`ComplexMaximalParabolicIntegrationStatement`: let `m` be a natural number and
`F ∈ principalSeries ℂ (m+1) (modulusCharacter (m+1))`. Then

`∫_{U(m+1)} F(κ) dκ = c_m · ∫_{ℂ^m} ∫_{U(m)} F(ι(k) J(v, 1)) dk dv`,

where

* `ι(k) = diag(k, 1)` (`iotaGL`);
* `J(v, 1)` (`chartGL v`) is the identity matrix with its last row replaced by `(v, 1)`. So
  `ι(k) J(v, 1)` is the block matrix with rows `(k, 0)` and `(v, 1)`, and `J(v, 1)` is the element `v`
  of the opposite unipotent radical of `P_{m,1}`;
* `c_m = (∫_ℂ |t|^{2m} e^{-|t|²} dt) / (∫_{ℂ^{m+1}} e^{-∑ |xᵢ|²} dx)`, written as integrals in Lean.
  It is positive (`chartConstant_pos`).

The inner integral is always finite because `F` is continuous on the compact set `ι(U(m)) J(v,1)`.
The outer integral is a Bochner integral, so the statement does not by itself say that the outer
integrand is integrable.

Provenance. Derived, internal infrastructure. For `F ∈ Ind_B^G δ_B` and a parabolic `P = M N`, the
identity `∫_K F = c ∫_{N̄} ∫_{K_M} F(k_M n̄) dk_M dn̄` is a standard consequence of
`(K ∩ P) \ K ≅ P \ G` and the density of the big cell `P N̄`. Here it is proved directly for
`P_{m,1}` of `GL_{m+1}(ℂ)`, with the explicit constant above, by matrix computations, without any
Haar measure on `GL_{m+1}(ℂ)`.

## Definitions

* Block matrices: `iota A = diag(A, 1)`, `dlast a = diag(1, …, 1, a)`, and `nP c`, the identity with
  the column `c` above the last diagonal entry. `topLeft p` is the upper left `m × m` block.
  `Jmat r` is the identity with its last row replaced by `r`, and `JGL r hr` is this matrix in
  `GL_{m+1}(ℂ)` when `r_m ≠ 0`. `chartGL v = JGL (Fin.snoc v 1) _`.
* `normSqC z = |z|²` as a complex number, and `modulusValue n a = ∏ᵢ (|aᵢ|²)^{(n−1)−2i}`, which is
  `principalSeriesCharacter ℂ n (modulusCharacter n) a` (`principalSeriesCharacter_modulus`).
* `iotaGL : GL_m(ℂ) →* GL_{m+1}(ℂ)` and `iotaK : U(m) → U(m+1)`.
* `leviSlice F y g = F(ι(g) y) |det g|⁻²` on `GL_m(ℂ)`.
* `natural F x = F^♮(x) = ∫_{U(m)} F(ι(k) x) dk`, and `naturalMat`, the same average for an arbitrary
  matrix through the Library's `unitsExtension` (extension by zero off `GL`).
* `phiF F r = F^♮(J(r)) |r_m|⁻² |r|^{2(m+1)}` if `r_m ≠ 0`, and `0` otherwise.
* `chartConstant m = gaussianMoment m / ∫ gaussian`.

## Proof

1. **Block algebra.** `ι` is multiplicative, compatible with `*`-conjugate transposes and commutes
   with `d(a)`; `ι(A) n(c) = n(A c) ι(A)`; `det ι(A) = det A`, `det n(c) = 1`, `det d(a) = a`,
   `det J(r) = r_m` (`J(r)` is lower triangular). A matrix `p` whose last row is `(0, …, 0, a)` with
   `a ≠ 0` factors as `p = n(c) ι(topLeft p) d(a)` with `c_i = p_{i,m}/a`
   (`eq_nP_mul_iota_mul_dlast`), so `det p = a · det(topLeft p)`.
2. **Covariance restricts to the Levi** (`leviSlice_covariant`, `leviSlice_mem`). For each `y`,
   `leviSlice F y` lies in the principal series of the modulus character of `GL_m(ℂ)`. Under `ι`,
   `diag(a)` becomes `diag(a, 1)` (`iotaGL_diagonalUnits`), `δ_{m+1}(a, 1) = δ_m(a) ∏ |aᵢ|²`
   (`modulusValue_lastCases`), upper unipotents map to upper unipotents
   (`iotaGL_mem_upperUnipotent`), and `|det|²` is smooth and nonvanishing on `GL_m(ℂ)`
   (`contDiff_det`, Mathlib's `contDiff_norm_sq`).
3. **Equivariance of `F^♮`.**
   * `natural_iota_mul`: `F^♮(ι(A) y) = |det A|² F^♮(y)`, from `ComplexKIntegralInvariance.integral_mul_eq`
     applied to `leviSlice F y` and right translation by `A`, using `|det k| = 1` on `U(m)`
     (`normSqC_det_unitary`).
   * `natural_dlast_mul`: `F^♮(d(a) x) = (|a|²)^{-m} F^♮(x)`, since `d(a)` commutes with `ι(k)` and
     `δ_{m+1}(1, …, 1, a) = (|a|²)^{-m}` (`modulusValue_dlast`).
   * `natural_nP_mul`: `F^♮(n(c) x) = F^♮(x)`, since `ι(k) n(c) = n(k c) ι(k)` and `F` is left
     invariant under upper unipotents (`covariant_upperUnipotent`).
   * `natural_mul_lastRow`: if the last row of `p` is `(0, …, 0, a)`, then
     `F^♮(p x) = |det p|² (|a|²)^{-(m+1)} F^♮(x)`, combining the three items with step 1.
4. **`F^♮` along last rows.** For `κ ∈ U(m+1)` with last row `r` and `r_m ≠ 0`, the matrix
   `p = J(r) κ⁻¹ = J(r) κ*` has last row `(0, …, 0, 1)` and `|det p|² = |r_m|²`, so
   `F^♮(J(r)) = |r_m|² F^♮(κ)` (`natural_Jmat_lastRow`). Since `J(s r) = d(s) J(r)`,
   `F^♮(J(s r)) = (|s|²)^{-m} F^♮(J(r))` (`natural_Jmat_smul`). Hence `phiF F` is homogeneous of degree
   zero under complex scalars (`phiF_homogeneous`), and `phiF F (lastRow κ) = F^♮(κ)` whenever the
   last entry of `lastRow κ` is nonzero, because `|lastRow κ| = 1` (`sqNorm_lastRow`,
   `phiF_lastRow`).
5. **Boundedness and measurability.** `phiF F` is bounded (`exists_bound_phiF`): every `r` with
   `r_m ≠ 0` is `t · lastRow κ₀` with `t = |r|` and `κ₀` from the complex Householder lemma
   `exists_unitary_lastRow`, so `phiF F r = F^♮(κ₀)` and `|F^♮| ≤ sup_{U(m+1)} |F|`. Measurability
   (`measurable_phiF`) comes from `StronglyMeasurable.integral_prod_right'` applied to
   `(r, k) ↦ unitsExtension F (ι(k) J(r))`, measurable because `unitsExtension F` is continuous on
   the open set of invertible matrices and zero off it (`measurable_unitsExtension`).
6. **Null set** (`ae_lastRow_last_ne_zero`). Apply the last-row formula
   `ComplexLastRowIntegral.integral_lastRow` to the indicator of `{x | x_m = 0}`, which is
   homogeneous of degree zero and vanishes on the chart `(v, 1)`. Hence the last entry of
   `lastRow κ` is nonzero for almost every `κ`.
7. **Averaging over the Levi compact** (`integral_eq_integral_natural`).
   `∫_{U(m+1)} F = ∫_{U(m+1)} F^♮`: `unitaryHaar m` is a probability measure, `∫ F(ι(k) κ) dκ = ∫ F(κ) dκ`
   by left invariance of `unitaryHaar (m+1)` (with `iotaK k`), and Fubini exchanges the integrals
   (the integrand is measurable and bounded by `sup_{U(m+1)} |F|`).
8. **Conclusion** (`integral_eq_chart`). By steps 7 and 6,
   `∫ F = ∫ F^♮(κ) dκ = ∫ phiF F (lastRow κ) dκ`. The last-row formula, with steps 4 and 5, turns this
   into `c_m ∫ phiF F (v, 1) (1 + |v|²)^{-(m+1)} dv`, and
   `phiF F (v, 1) (1 + |v|²)^{-(m+1)} = F^♮(J(v, 1))` (`phiF_snoc`, via `sqNorm_snoc`).
   `chartConstant_pos` uses `gaussianMoment_pos` (the integrand is positive off `0`, and the
   complement of a point has positive Lebesgue measure) and `integral_gaussian_pos`.
