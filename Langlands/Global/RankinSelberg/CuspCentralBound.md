# Cusp forms grow at most like a fixed power of `|det|`

Module `Langlands.Global.RankinSelberg.CuspCentralBound`, namespace
`Langlands.Global.RankinSelbergGlobal.CuspCentralBound`. It is a helper
module for `UnequalGaugeReduction` and contains only theorems: no new
definitions and no statements.

Provenance: internal. This is the standard fact that a cusp form with a
central character is bounded modulo the centre. For a cuspidal
realization with a central character, the module turns that fact into a
power bound on all of `GL_n(𝔸)`. The exponent depends only on the
realization; the constant depends on the vector.

## Results

- `exists_norm_evaluate_le_of_absDet_eq_one`: for a cuspidal
  `OperatorRealization` `S` and a vector `f`, the realized function
  `evaluate F n (S.toContinuous f)` is bounded on the adelic matrices `g`
  with `absDet F n g = 1`.
- `expUnit_zero`, `expUnit_neg`, `continuous_expUnit`: elementary facts
  about the Library map `expUnit : ℝ → ℝ≥0ˣ`, `y ↦ e^y`.
- `exists_norm_character_expUnit`: for a continuous character
  `ω : ℝ≥0ˣ →ₜ* ℂˣ` there is a real `α` with `‖ω(e^y)‖ = exp(α y)` for
  all real `y`.
- `absDet_scalar_full_expUnit`: the scalar matrix of the positive real
  idele `PositiveRealIdeles.full F (e^y)` has
  `absDet = exp([F:ℚ] · n · y)`.
- `exists_norm_evaluate_le_rpow` (the central power bound): for `n ≠ 0`,
  a cuspidal `S` with central character `χ` (`S.HasCentralCharacter χ`),
  there is `β : ℝ` such that for every vector `f` there is `C ≥ 0` with
  `‖evaluate F n (S.toContinuous f) g‖ ≤ C * absDet F n g ^ β` for all
  `g ∈ GL_n(𝔸)`.
- `detNorm_eq_absDet`: `detNorm F n g` is `absDet` of the image of `g`
  under `GeneralLinearGroupPoints.adelicHomeomorph` (definitional).
- `exists_norm_cuspFunction_le`: for an actual cuspidal realization
  `T' : CuspidalOperatorRealization F t` there is `β : ℝ` such that for
  every `v'` there is `C ≥ 0` with
  `‖cuspFunction F T' v' g‖ ≤ C * detNorm F (t + 1) g ^ β` for all
  `g : Points F (t + 1)`.
- `detNorm_dualPoint`: `detNorm F n (dualPoint F n g) = (detNorm F n g)⁻¹`,
  where `dualPoint F n g = w ᵗg⁻¹` with `w` the long Weyl element.
- `exists_norm_dualCuspFunction_le`: the same power bound, with exponent
  `-β`, for the dual function `dualFunction F (t + 1) (cuspFunction F T' v')`.

## Proofs

**Norm-one bound.** `exists_siegelDecomposition` writes each `g` as
`γ · x · q`. Here `γ` is rational, `x` lies in the archimedean torus with
logarithmic coordinates in the Siegel chamber, and `q` lies in a fixed
compact set `Q₁`. When `absDet g = 1`, the product formula
(`absDet_rational_mul`) and `UnequalAnalytic.log_absDet_torInf_mul` show
that the sum of the coordinates of `x` is bounded in absolute value by
`L / [F:ℚ]`, where `L` bounds `|log absDet|` on `Q₁`
(`UnequalAnalytic.exists_abs_log_absDet_le`). The chamber estimate
`OperatorRealization.exists_chamber_decay`, used with decay rate `0`,
then gives a uniform bound at `x q`. Left invariance under rational
points (`evaluate_rational`) carries this bound to `g`.

**Characters of `ℝ≥0ˣ`.** The map `y ↦ log ‖ω(e^y)‖` is a continuous
additive endomorphism of `ℝ`, hence `ℝ`-linear (`map_real_smul`), so it
equals `y ↦ α y` with `α` its value at `1`.

**Power bound.** By `OperatorRealization.irreducibleCentralCharacter` the
irreducible realization has a central character `χ`. Restricting `χ` to the
positive real ideles `PositiveRealIdeles.full F` gives a character of
`ℝ≥0ˣ` with `‖·‖ = exp(α y)`. Write `k = [F:ℚ] n` and
`y = -log(absDet g) / k`. Then the scalar `z = full(e^y)` has
`absDet(z g) = 1`, so the norm-one bound applies at `z g`. The central
character identity `S.centralCharacter_evaluate` gives
`‖φ(z g)‖ = exp(α y) ‖φ(g)‖`. Hence
`‖φ(g)‖ ≤ exp(-α y) C = C · absDet(g)^(α/k)`, and `β = α / k` does not
depend on the vector.

**Cusp functions and duals.** `UnequalAnalytic.cuspFunction_eq` identifies
`cuspFunction` with the realized function at the image point, so the
power bound transfers. For the dual function, `dualFunction_eq` rewrites
it as the cusp function at `dualPoint g`. The determinant norm of the long
Weyl element is a unit whose square is `1`, so it equals `1`. The
inverse transpose has inverse determinant. Together these give
`detNorm(dualPoint g) = detNorm(g)⁻¹`, so the bound holds with exponent
`-β`.
