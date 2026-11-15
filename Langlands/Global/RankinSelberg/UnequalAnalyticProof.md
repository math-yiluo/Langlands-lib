# Proof of the global analytic theory for unequal-rank cuspidal pairs

This module proves `Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement`. That is
the analytic and functional-equation part of J. W. Cogdell, *Analytic theory of
L-functions for GL_n* (2004), §2.2, Theorem 2.1 (printed p.207; the convergence discussion is
on p.205; source `cogdell-2004-analytic-theory-gln`). The proof is the theorem

```
theorem Langlands.Global.RankinSelbergGlobal.UnequalAnalytic.unequalAnalyticStatement_proof :
    UnequalAnalyticStatement.{u}
```

It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Route

Cogdell states that the integral converges absolutely for all `s`, uniformly on compact sets,
"since the cusp forms are rapidly decreasing", and hence is entire and bounded in vertical
strips (printed p.205, PDF p.208). He derives the functional equation from the outer
automorphism `g ↦ ᵗg⁻¹` (printed pp.206–207, PDF pp.209–210). The formal proof follows this
route. The Library's rapid-decay results only cover
matrices whose determinant lies in a fixed band. Two decay facts are therefore proved in the
supporting modules, both for an unbounded determinant:

1. the projection `g ↦ P φ (diag(g, 1))` decays faster than every `exp (-N |log |det g||)`
   (`exists_norm_projection_pad_le`, module `UnequalAnalyticProjection`). Its proof
   uses `exists_norm_le_of_basis_column_row` (module `UnequalAnalyticDecay`, built on the
   Library Siegel decomposition and the heights of `UnequalAnalyticHeights`): every matrix
   `y diag(g, I)` with `y ∈ Y(𝔸)` has a standard basis column and a standard basis row;
2. the cusp form `φ'` on `GL_m` has `∫_{GL_m(F) \ GL_m(𝔸)} |φ'| exp (-B |log |det||) < ∞` for
   large `B` (`exists_lintegral_quotient_lt_top`, module `UnequalAnalyticIntegrability`).

## `analytic_main`

The main theorem `analytic_main` is stated for abstract data. Here `ψ` is continuous, trivial
on `F` and of norm one. `φ` on `GL_(r+1)(𝔸)` is continuous, left invariant under rational
points, and satisfies `HasBasisDecay`. `φ'` on `GL_(t+1)(𝔸)` is continuous, left invariant,
and satisfies the weighted integrability of item 2. Its conclusion is exactly the conclusion
of the target statement for these functions. With `m = t + 1`, `Γ = GL_m(F)`, and `μ̄` the
Library quotient measure `rationalQuotientHaarMeasure F (Scheme F m)`, the steps are:

- **Descended functions.** `P g = projection … (pad g)` is continuous and left
  `Γ`-invariant (`continuous_projection_pad`, `projection_pad_rational_mul`). Hence
  `A_g = P · φ'` and `L_g = log |det|` descend to continuous functions `A`, `L` on
  `Γ \ GL_m(𝔸)` (`LeftCosetSpace.lift`, invariance of `|det|` by `detNorm_rational_mul`).
  The integrand, evaluated at the representative `out q`, equals
  `A q · exp ((s - 1/2) L q)` (`lift_eq_out`, definition of `detPower`).
- **Exponential moments.** For each real `σ`, `‖A‖ exp (σ L)` is integrable. Choose
  `B = max B₀ 0` from item 2, and `C` with `|P g| ≤ C exp (-(B + |σ|) |L_g|)` from item 1. Then
  `‖A‖ exp (σ L) ≤ C |φ'| exp (-B |L|)`, since `σ L ≤ |σ| |L|`, and
  `integrable_of_enorm_le` applies.
- **Clauses 1, 3, 4.** The generic module `UnequalAnalyticHolomorphy` gives the following for
  `J(s) = ∫ A exp (s L) dμ̄`: absolute integrability for every `s`
  (`integrable_mul_cexp`), differentiability on `ℂ` (`differentiable_integral_mul_cexp`,
  differentiation under the integral), and bounds on vertical strips
  (`exists_norm_integral_mul_cexp_le`). Since `I(s) = J(s - 1/2)`, these give clauses 1, 3
  and 4. The strip `[a, b]` for `I` is the strip `[a - 1/2, b - 1/2]` for `J`.
- **Transpose inverse on the quotient.** `ι = iotaEquiv F m` maps `Γ` onto itself
  (`iota_rational`, `iota_iota`). It induces a measurable bijection `ῑ` of `Γ \ GL_m(𝔸)`
  (`cosetMeasurableEquiv`, module `UnequalAnalyticQuotientMeasure`). Since `ι` is an
  involution, its Haar character is `1` (`mulEquivHaarChar_eq_one_of_involutive`), so
  `ι` preserves Haar measure (`map_haar_eq_smul`) and `ῑ` preserves `μ̄`
  (`map_cosetMap_discreteQuotientMeasure`). Representatives give
  `ῑ q = Γ ι(out q)`.
- **The dual integrand.** For every `s`, the dual integrand of `φdual`, `φ'dual` at `q` equals
  `A (ῑ q) exp ((1/2 - s) L (ῑ q))`. Here `dualProjection` of `φdual` is the projection of
  `φ` at `ι p`, since `φdual ∘ ι = φ` (`dualFunction_iota`: the long Weyl element is rational
  and `φ` is invariant). Also `ι (pad g) = pad (ι g)` (`iota_pad`),
  `φ'dual = φ' ∘ ι` (`dualFunction_eq`), and `log |det ι g| = -log |det g|`
  (`detNorm_iota`).
- **Clause 2.** The dual integrand is the integrable function `A exp ((1/2 - s) L)` composed
  with the measure-preserving `ῑ` (`MeasurePreserving.integrable_comp_emb`).
- **Clause 5 (functional equation).**
  `I(s) = ∫ A exp ((s - 1/2) L) dμ̄ = ∫ (A exp ((s - 1/2) L)) ∘ ῑ dμ̄ = Ĩ(1 - s)`, by
  `MeasurePreserving.integral_comp'` and the formula for the dual integrand at `1 - s`
  (`1/2 - (1 - s) = s - 1/2`).

## Cusp forms

- `cuspFunction_eq`: the function `cuspFunction F T v` of a realized vector is the ambient
  evaluation of `T.realization.toContinuous v` at `e x`, where `e` is
  `GeneralLinearGroupPoints.adelicHomeomorph`. This follows from the Library comparison
  `evaluate_continuousGeneralLinearEquiv_at_point`.
- `continuous_cuspFunction` (`continuous_evaluate`), `cuspFunction_rational_mul`
  (`evaluate_rational`, `adelicHomeomorph_rational`), and `hasBasisDecay_cuspFunction`
  (`exists_norm_le_of_basis_column_row` for the cuspidal realization; `0 < r + 1`).
- `unequalAnalyticStatement_proof`: unpack `IsStandardAdditiveCharacter` (continuity,
  triviality on `F`, norm one; nontriviality is not needed). Obtain item 2 for `φ'` from
  `exists_lintegral_quotient_lt_top` and `cuspFunction_eq`, and apply `analytic_main`.

## Supporting modules

The proof imports the following modules, all in `Langlands/Global/RankinSelberg/`, each with
its own Markdown description: `UnequalAnalyticHeights`, `UnequalAnalyticDecay`,
`UnequalAnalyticHolomorphy`, `UnequalAnalyticQuotientMeasure`, `UnequalAnalyticMatrices`,
`UnequalAnalyticPoints`, `UnequalAnalyticProjection`, `UnequalAnalyticIntegrability`.
