# The `O(n)`-integral in coordinates of the maximal parabolic subgroup `P_{n-1,1}`

Lean module: `Langlands.Representation.Archimedean.MaximalParabolicIntegration`.

This module writes the integral over `O(m+1)` of a function in the principal series of the modulus
character `δ_B` as an integral over the opposite unipotent radical of the maximal parabolic
subgroup `P_{m,1}`, followed by an integral over the Levi compact `O(m)`. The statement is
`Langlands.Archimedean.MaximalParabolicIntegrationStatement`, proved as
`Langlands.Archimedean.maximalParabolicIntegration`.

In the planned proof of `RealStandardLanglandsQuotientStatement` (Task 6749), this formula turns
the `O(n)`-pairing of the Library's `RealPrincipalSeriesDuality` into an iterated integral. The
partial Jacquet integral over `P_{n-1,1}` and its limit argument are then applied to that iterated
integral.

Notation: `O(n)` is the subgroup `unitaryCompact ℝ n` of `Langlands.GeneralLinear n ℝ`, with the
Library's normalized Haar measure `RealPrincipalSeriesDuality.haarK n` for its Borel σ-algebra
(`measurableSpaceK`). Row vectors are `Fin m → ℝ` with Lebesgue measure. `Fin.snoc v 1` is the row
vector `(v, 1)`. Indices run over `Fin (m+1) = {0, …, m}`, and `Fin.last m` is the last index.
Declarations without a prefix are in the namespace
`Langlands.Archimedean.MaximalParabolicIntegration`.

## The statement

`MaximalParabolicIntegrationStatement`: let `m` be a natural number and
`F : GL_{m+1}(ℝ) → ℂ` be

* smooth (`ContMDiff (matrixModel ℝ (m+1)) 𝓘(ℝ, ℂ) ∞ F`),
* left covariant under the upper triangular Borel subgroup by its modulus character
  (`IsModulusCovariant F`): for every `a ∈ (ℝˣ)^{m+1}`, every upper unipotent `u` and every `g`,
  `F(diag(a) u g) = ∏ᵢ |aᵢ|^{m − 2i} F(g)`.

Then

`∫_{O(m+1)} F(κ) dκ = c_m · ∫_{ℝ^m} ∫_{O(m)} F(ι(k) J(v, 1)) dk dv`,

where

* `ι(k) = diag(k, 1)` (`iotaGL`);
* `J(v, 1)` (`chartGL v`) is the identity matrix with its last row replaced by `(v, 1)`. So
  `ι(k) J(v, 1)` is the block matrix with rows `(k, 0)` and `(v, 1)`, and `J(v, 1)` is the element
  `v` of the opposite unipotent radical of `P_{m,1}`;
* `c_m = (∫_ℝ |t|^m e^{-t²} dt) / (∫_{ℝ^{m+1}} e^{-∑ xᵢ²} dx)`, written as integrals in Lean. It is
  positive (`chartConstant_pos`).

The inner integral is always finite because `F` is continuous on the compact set `ι(O(m)) J(v,1)`.
The outer integral is a Bochner integral, so Lean's statement does not by itself say that the
outer integrand is integrable.

Provenance. Derived, internal infrastructure. For `F ∈ Ind_B^G δ_B` and a parabolic `P = M N`,
the identity `∫_K F = c ∫_{N̄} ∫_{K_M} F(k_M n̄) dk_M dn̄` is a standard consequence of the
identification `(K ∩ P) \ K ≅ P \ G` and the density of the big cell `P N̄`. Here it is proved
directly for `P_{m,1}` of `GL_{m+1}(ℝ)`, with the explicit constant above, by matrix computations.
The proof uses no Haar measure on `GL_{m+1}(ℝ)`.

## Definitions

* Block matrices: `iota A = diag(A, 1)`, `dlast a = diag(1, …, 1, a)`, and `nP c`, the identity
  with the column `c` above the last diagonal entry. `topLeft p` is the upper left `m × m` block.
  `Jmat r` is the identity with its last row replaced by `r`, and `JGL r hr` is this matrix in
  `GL_{m+1}(ℝ)` when `r_m ≠ 0`. `chartGL v = JGL (Fin.snoc v 1) _`.
* `modulusCharacter n a = ∏ᵢ |aᵢ|^{(n−1)−2i}` and `IsModulusCovariant F` as in the statement.
  `isModulusEquivariant_of_covariant` shows that this implies the Library's
  `RealPrincipalSeriesDuality.IsModulusEquivariant`.
* `iotaGL : GL_m(ℝ) →* GL_{m+1}(ℝ)` and `iotaK : O(m) → O(m+1)`.
* `leviSlice F y g = F(ι(g) y) |det g|⁻¹` on `GL_m(ℝ)`.
* `natural F x = F^♮(x) = ∫_{O(m)} F(ι(k) x) dk`.
* `phiF F r = F^♮(J(r)) |r_m|⁻¹ |r|^{m+1}` if `r_m ≠ 0`, and `0` otherwise. In Lean it is written
  through `naturalMat`, the same average for an arbitrary matrix, using the Library's
  `unitsExtension` (extension by zero off `GL`).
* `chartConstant m = gaussianMoment m / ∫ gaussian`, with `gaussianMoment` and `gaussian` from
  `OrthogonalLastRowIntegral`.

## Proof

1. **Block algebra.** `ι` is multiplicative and commutes with `d(a)`. `ι(A) n(c) = n(A c) ι(A)`.
   `det ι(A) = det A`, `det n(c) = 1`, `det d(a) = a` and `det J(r) = r_m`. `J(r)` is lower
   triangular. A matrix `p` whose last row is `(0, …, 0, a)` with `a ≠ 0` factors as
   `p = n(c) ι(topLeft p) d(a)` with `c_i = p_{i,m}/a` (`eq_nP_mul_iota_mul_dlast`). Hence
   `det p = a · det(topLeft p)`.
2. **Covariance restricts to the Levi** (`leviSlice_covariant`, `contMDiff_leviSlice`). For each
   `y`, `leviSlice F y` is smooth on `GL_m(ℝ)` and modulus-covariant there. Under `ι`, the
   diagonal `diag(a)` of `GL_m` becomes `diag(a, 1)` (`iotaGL_diagonalUnits`), and the modulus
   characters satisfy `δ_{m+1}(a, 1) = δ_m(a) ∏ |aᵢ|` (`modulusCharacter_lastCases`). Upper
   unipotents map to upper unipotents (`iotaGL_mem_upperUnipotent`).
3. **Equivariance of `F^♮`.**
   * `natural_iota_mul`: `F^♮(ι(A) y) = |det A| F^♮(y)`. Apply the accepted
     `KIntegralInvariance.integral_mul_eq` (the `O(m)`-integral of a smooth modulus-equivariant
     function on `GL_m(ℝ)` is right `GL_m(ℝ)`-invariant) to `leviSlice F y` and right translation
     by `A`, using `|det k| = 1` on `O(m)` (`abs_det_unitary`).
   * `natural_dlast_mul`: `F^♮(d(a) x) = |a|^{-m} F^♮(x)`. `d(a)` commutes with `ι(k)`, and
     `δ_{m+1}(1, …, 1, a) = |a|^{-m}`.
   * `natural_nP_mul`: `F^♮(n(c) x) = F^♮(x)`. `ι(k) n(c) = n(k c) ι(k)` and `F` is left invariant
     under upper unipotents.
   * `natural_mul_lastRow`: if the last row of `p` is `(0, …, 0, a)`, then
     `F^♮(p x) = |det p| |a|^{-(m+1)} F^♮(x)`. Combine the three items with step 1.
4. **`F^♮` along last rows.** For `κ ∈ O(m+1)` with last row `r` and `r_m ≠ 0`, the matrix
   `p = J(r) κ⁻¹` has last row `(0, …, 0, 1)` and `|det p| = |r_m|`. So
   `F^♮(J(r)) = |r_m| F^♮(κ)` (`natural_Jmat_lastRow`). Since `J(s r) = d(s) J(r)`, also
   `F^♮(J(s r)) = |s|^{-m} F^♮(J(r))` (`natural_Jmat_smul`).
   Consequently `phiF F` is homogeneous of degree zero (`phiF_homogeneous`), and
   `phiF F (lastRow κ) = F^♮(κ)` whenever the last entry of `lastRow κ` is nonzero, because
   `|lastRow κ| = 1` (`sqNorm_lastRow`, `phiF_lastRow`).
5. **Boundedness and measurability.** `phiF F` is bounded (`exists_bound_phiF`). Every nonzero
   `r` with `r_m ≠ 0` equals `t · lastRow κ₀` with `t = |r|`, where `κ₀` is the orthogonal matrix
   from the Householder lemma `OrthogonalLastRowIntegral.exists_orthogonal_lastRow`. By
   homogeneity and step 4, `phiF F r = F^♮(κ₀)`, and `|F^♮| ≤ sup_{O(m+1)} |F|`.
   Measurability (`measurable_phiF`) comes from `StronglyMeasurable.integral_prod_right'` applied
   to `(r, k) ↦ unitsExtension F (ι(k) J(r))`. That function is measurable because
   `unitsExtension F` is continuous on the open set of invertible matrices and zero off it
   (`measurable_unitsExtension`).
6. **Null set** (`ae_lastRow_last_ne_zero`). Apply the accepted last-row formula
   `OrthogonalLastRowIntegral.integral_lastRow` to the indicator `Φ₀` of `{x | x_m = 0}`, which is
   homogeneous of degree zero. Its chart integrand `Φ₀(v, 1)` vanishes, so
   `∫_{O(m+1)} Φ₀(lastRow κ) dκ = 0`. Hence the last entry of `lastRow κ` is nonzero for almost
   every `κ`.
7. **Averaging over the Levi compact** (`integral_eq_integral_natural`).
   `∫_{O(m+1)} F = ∫_{O(m+1)} F^♮`. `haarK m` is a probability measure, and for each `k ∈ O(m)`,
   `∫ F(ι(k) κ) dκ = ∫ F(κ) dκ` by left invariance of `haarK (m+1)` (`integral_mul_left_eq_self`
   with `iotaK k`). Exchange the two integrals by Fubini (`integral_integral_swap`). The function
   `(k, κ) ↦ F(ι(k) κ)` is measurable (continuous matrix entries composed with
   `unitsExtension F`) and bounded by `sup_{O(m+1)} |F|`.
8. **Conclusion** (`integral_eq_chart`). By steps 7 and 6,
   `∫ F = ∫ F^♮(κ) dκ = ∫ phiF F (lastRow κ) dκ`. The last-row formula, with steps 4 and 5, turns
   this into `c_m ∫ phiF F (v, 1) (1 + |v|²)^{-(m+1)/2} dv`. Finally,
   `phiF F (v, 1) = F^♮(J(v, 1)) (1 + |v|²)^{(m+1)/2}` (`phiF_snoc`, via `sqNorm_snoc`).
   `maximalParabolicIntegration` restates this, after unfolding `chartConstant` and `natural`.

`chartConstant_pos` (`c_m > 0`) uses `gaussianMoment_pos` (the integrand `|t|^m e^{-t²}` is
positive on `(0, ∞)`) and `OrthogonalLastRowIntegral.integral_gaussian_pos`.
