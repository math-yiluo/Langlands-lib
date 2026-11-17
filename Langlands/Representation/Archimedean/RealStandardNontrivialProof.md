# Real standard modules are nonzero

Author: Worker 3657. Module `Langlands.Representation.Archimedean.RealStandardNontrivialProof`.
It proves that every real standard module `realStandardModule n ds` has a nonzero `O(n)`-finite
function. This is the real-place input of the Task 7003 proof
(`CuspidalArchimedeanStandardGenericStatement`); the complex analogue is the Library theorem
`complexStandardNontrivial`. It changes no published file.

Task 7400 also uses this theorem: its `RealPlaceAnalyticReduction` adapter
discharges the real-standard nonvanishing premise of the parameter-determinant
comparison.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`. `realStandardModule`, `kFiniteFunctions`,
`unitaryCompact`, `blockRotation`, `blockFourierCoefficient`, `realInducedBlockAt` and
`mem_realStandardModule_iff` are the Library's (module `StandardModule`). `rotMatrix h θ`,
`ia h`, `ib h` and `blockRotation_val_eq` come from the Library module `RealBlockRotation`.
`rotMatrix h θ` is the rotation `r(θ)` by `θ` in the coordinates `p, p + 1`, the matrix of
`blockRotation n p θ` (with `h : p + 1 < n`). `PrincipalSeriesExtension.extension_eq` is the
Library's value formula for the extension at `x = b κ`. `gramFunction`,
`gramFunction_mem_kFiniteFunctions`, `gramFunction_one` and `gramFunction_eq_extension` come from
`RealGramFunction`. `blockPoly`, `blockFactor`, `lplus`, `lminus`, `DependsOnRows` and
`IsRowRotation` come from `RealStandardBlockPolynomial`. `integrand`, `rotP`, `rotQ`,
`integral_integrand_eq_zero` and `continuous_integrand` come from
`Langlands.Analysis.InversePowerFourier`.

## Main theorem

```lean
theorem Langlands.Archimedean.realStandardNontrivial :
    ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
      Nontrivial (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
```

For every list `ds` of real blocks of total rank `n`, the space of `O(n)`-finite functions of the
real standard module `realStandardModule n ds` is nonzero. It replaces the nonvanishing hypothesis
of an earlier partial Task 7003 draft. The space is the Library abbreviation
`realStandardKFinite ds` (module `ArchimedeanPlaceParameter`) at `n = realRank ds`.

Supporting results:

```lean
theorem Langlands.Archimedean.gramFunction_blockPoly_mem (n : ℕ) (ds : List RealBlock)
    (hds : realRank ds = n) :
    gramFunction (shiftedExponent n (realPositionExponent ds)) (blockPoly n ds 0) ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

theorem RealStandardNontrivial.blockFourierCoefficient_eq_zero (s : Fin n → ℂ) {N : ℕ}
    (hs : s (ia h) - s (ib h) = N)
    {R : MvPolynomial (Fin n × Fin n) ℂ} (hR : DependsOnRows {l | l ≠ p ∧ l ≠ p + 1} R) {k : ℤ}
    (hk : |k| < N) (g : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n p k (gramFunction s (blockFactor n p N * R)) g = 0
```

## The nonzero vector

The vector is `f = gramFunction s P` with `s = shiftedExponent n (realPositionExponent ds)` and
`P = blockPoly n ds 0`.

* **Principal series and `O(n)`-finiteness.** `P` has the sign parity of the position characters
  (`hasSignParity_blockPoly`), so `gramFunction_mem_kFiniteFunctions` (with the Library identity
  `realPositionCharacter_eq_signUnit_mul`) puts `f` in the `O(n)`-finite functions of the
  principal series `principalSeries ℝ n (realPositionCharacter ds)`.
* **Fourier conditions.** Let `d` be an induction block at the positions `p, p + 1`, and
  `N = |d.weight| + 1`. Then `P = Φ_p · R` with `R` free of rows `p, p + 1`
  (`exists_blockPoly_eq_blockFactor_mul`). Moreover
  `s_p - s_{p+1} = |d.weight| + 1 = N`: the shift in `shiftedExponent` adds `1`, and
  `realPositionExponent_of_blockAt` gives `|d.weight|`. The Library condition asks
  `blockFourierCoefficient n p k f g = 0` for `|k| < |d.weight|`, hence for `|k| < N`. That is
  `blockFourierCoefficient_eq_zero`.
* **Nonvanishing.** `f(1) = P(1) ≠ 0` (`gramFunction_one`, `eval_one_blockPoly_ne_zero`).

## Proof of the Fourier vanishing

Fix `g`, an induction block at `p, p + 1` and `|k| < N`.

1. **Iwasawa decomposition.** `g = b κ` with `b = diag(a) u` upper triangular with nonzero
   diagonal and `κ ∈ O(n)` (Library `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`).
2. **Rotations** (`rotMatrix_mul_apply`, `mul_rotMatrix_transpose_apply`). `r(θ)` rotates the rows
   `p, p + 1` and `r(φ)ᵀ` rotates the columns `p, p + 1`. In `r(θ) b` the only entry below the
   diagonal is `c' = sin θ · b_pp` at `(p + 1, p)` (`rotMatrix_mul_apply_eq_zero`). The new
   diagonal entry is `d' = sin θ · b_{p,p+1} + cos θ · b_{p+1,p+1}` (`bottomLeft`,
   `bottomRight`).
3. **Re-triangularization.** Polar coordinates (`exists_polar`) give `ρ > 0` and `φ` with
   `(cos φ, sin φ) ρ = (d', c')`. Then `r(θ) b r(φ)ᵀ` is upper triangular
   (`rotated_isUpperTriangular`). Its diagonal is `b_ll` off the block,
   `b_pp b_{p+1,p+1} / ρ` at `p` and `ρ` at `p + 1` (`rotated_ia_eq`, `rotated_ib`).
   Also `r(θ) b κ = (r(θ) b r(φ)ᵀ) (r(φ) κ)` (`rotMatrix_mul_eq`).
4. **Value formula** (`gramFunction_blockRotation_mul`, `prod_abs_rotated_cpow`,
   `gramFunction_blockRotation_eq`). By `PrincipalSeriesExtension.extension_eq`, the value of `f`
   at `r(θ) g` is `∏_l |diagonal_l|^(s_l)` times `P` at the sign-normalized rows of `r(φ) κ`. The
   product equals a `θ`-independent constant times `ρ^(-N)`, since `s_p - s_{p+1} = N`. The rows
   of `r(φ) κ`, normalized by signs, are a row rotation by `(cos φ, σ sin φ)` of the
   `θ`-independent entries `baseEntries` (`isRowRotation_rotated`). Here
   `σ = sgn(b_pp) sgn(b_{p+1,p+1})` (`blockSign`). By `eval_rotated_blockFactor_mul` and
   `inv_pow_mul_sub_eq`/`inv_pow_mul_add_eq`, `f(r(θ) g)` equals
   `C · (L₊^N (d' + iσc')^(-N) + (-1)^N L₋^N (d' - iσc')^(-N))`. The constants `C`, `L₊`, `L₋` do
   not depend on `θ`.
5. **Fourier coefficients.** `d' ± iσc'` is `P' e^{iθ} + Q' e^{-iθ}` with `P' = rotP(∓σ b_pp, …)`
   and `Q' = rotQ(∓σ b_pp, …)` (`bottom_add_eq`, `bottom_sub_eq`, from `rotated_bottom_eq`). The
   matrix `[[∓σ b_pp, b_{p,p+1}], [0, b_{p+1,p+1}]]` is invertible, so `‖P'‖ ≠ ‖Q'‖`
   (`norm_rotP_ne_norm_rotQ`). Each term then has vanishing Fourier coefficients for `|k| < N`
   (`integral_integrand_eq_zero`). The integral of the sum splits because both terms are
   continuous (`continuous_integrand`).

## Provenance

That standard modules are nonzero is standard: the induced representations are nonzero. The Task
7003 contract suggests a raising/lowering-operator argument for the Fourier condition. This proof
instead uses an explicit `GL_2` computation: in `GL_2(ℝ)`, the function `(d - i c)^(-N)` of the
bottom row has only `SO(2)`-weights `|k| ≥ N`. It is spread over the induction blocks through the
Gram–Schmidt formula of the Library module `PrincipalSeriesExtension`. The argument was written
within the project and claims no literature source.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` against Library
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`: check 949e5803. It built `InversePowerFourier`,
`RealGramFunction`, `RealStandardBlockPolynomial` and this module with no errors or warnings.
Axioms of `Langlands.Archimedean.realStandardNontrivial`: `propext`, `Classical.choice`,
`Quot.sound`. Checks 91e91b10 and 4280e258 rebuilt the four modules together with the Task 7003
proof module `CuspidalArchimedeanStandardGenericProof`, again with no errors or warnings.
