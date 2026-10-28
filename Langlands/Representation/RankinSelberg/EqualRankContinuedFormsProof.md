# Construction of the continued normalized equal-rank trilinear forms

Author: Worker 233.

The paired Lean file proves

```text
theorem Langlands.RankinSelberg.equalRankContinuedForms {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankContinuedFormsStatement.{uF, uV, uW} F T n
```

with independent universes `uF`, `uV`, `uW`. It uses only the three explicit
analytic hypotheses of the statement (the original and the dual
`EqualRankAnalyticConclusion` and `RowFourierClosed ψ ν (n+1)`) together with the
compatibility of the quotient measure. The Whittaker-type hypotheses and the
nonvanishing of `ℓ` and `ℓ'` are not needed and are left unused. Hence the
full supplied scope is kept: reducible representations, every compatible
quotient measure, every scalar additive Haar measure `ν`, and every pair of
normalized generators `P`, `Pdual`.

## Modules used

All imports are published Library modules (Library commit
`65f39f42712a45624ccc76ac5da7b60f52ebcd6f`). Two of them are helper modules
written for this proof and published through the helper tasks
`28187cfe-fdc3-4489-8631-36882b53e61a` (accepted artifact
`059e3cba-bbd1-4826-9922-d51243476eb7`) and
`bd2991bb-7582-4786-bb5b-da489d7eb049` (accepted artifact
`ec840fe4-72a1-4135-8f68-464bfd9a458e`); each has its own Markdown:

- `Langlands.Representation.RankinSelberg.LaurentEvaluation`: evaluation
  `laurentEval x` of Laurent coefficients at a unit `x : ℂˣ`, the bridge
  `laurentEval_eq_of_laurentToRatFunc_eq` to rational evaluation with a guard
  on one factor only, spectral units `spectralUnit hq s` with value
  `spectralPoint q s`, linear Laurent lifts `laurentLift`, and composition of
  curried trilinear maps (`trilinearPostcomp`, `trilinearPrecomp`).
- `Langlands.Representation.RankinSelberg.EqualRankContinuationFamily`:
  linearity of the equal-rank integrals on common regions of absolute
  convergence, their right-translation law, the trilinear rational
  continuation family `equalRankContinuationFamily hq hA` with its `X^m`
  translation law, and compatibility of the dual model maps with translation.

The other imports are:

- the target statement module;
- `PadicRowFourierEquivarianceProof`, which supplies the Fourier matrix change
  of variables;
- `PadicScalarHaarScalingProof`, which supplies second countability and
  sigma-compactness of the p-adic topology;
- `LocalField.Normalization.Proof`, which supplies `residueCardinality_gt_one`
  and `normalizedAbs_of_ne_zero` for the supplied topological data.

## Row Fourier transform as a linear map

`rowFourierMap (h : RowFourierClosed ψ ν d)` is the complex-linear map on row
Schwartz–Bruhat functions sending `Φ` to the Schwartz–Bruhat function chosen
by `h Φ`, whose values are the row Fourier integrals of `Φ`. A Schwartz–Bruhat
function is determined by its values (`IsRowFourierPair.unique`). So
additivity and homogeneity follow from the linearity of the published
`rowFourierTransform`. This needs a Borel structure on the row space and a
sigma-finite scalar Haar measure.

- `isRowFourierPair_rowFourierMap`: `Φ` and `rowFourierMap h Φ` form a row
  Fourier pair.
- `eq_rowFourierMap`: any row Fourier partner of `Φ` equals
  `rowFourierMap h Φ`.
- `rowFourierMap_translate`: assume an equivariance law of the form proved by
  the p-adic equivariance theorem, for an arbitrary absolute value `abv`. Then
  the transform of a right translate `Φg` (with `Φg x = Φ (x g)`) equals
  `(abv (det g))⁻¹ • Ψ`, where `Ψ x = rowFourierMap h Φ (x (g⁻¹)ᵀ)` is the
  translate of the transform by `inverseTranspose d F g`. This is the
  identity `(ρ(g)Φ)^ = |det g|^(-1) ρ(gᶥ)Φ^` of JPSS §2.10, where
  `gᶥ = (g⁻¹)ᵀ`.

## Determinants and the dual spectral factor

`det_inverseTranspose` gives `det (g⁻¹)ᵀ = (det g)⁻¹`, and
`abv_det_inverseTranspose` gives the same identity after applying any
absolute value. `dual_spectral_factor (hq : 0 < q) (m : ℤ) (s : ℂ)` states

```text
((q : ℝ) ^ m)⁻¹ * spectralPoint q (1 - s) ^ (-m) = spectralPoint q s ^ m,
```

where `spectralPoint q s = q ^ (-s)`. It follows from
`q^(-(1-s)) = q⁻¹ q^s` (via `Complex.cpow_sub`).
`laurentEval_spectralUnit_T_mul` and `laurentEval_spectralUnit_dual_factor`
restate the two evaluations used below:

```text
laurentEval (spectralUnit hq0 s) (T m * a)
  = spectralPoint q s ^ m * laurentEval (spectralUnit hq0 s) a
laurentEval (spectralUnit hq0 (1 - s)) ((q ^ m)⁻¹ • (T (-m) * a))
  = spectralPoint q s ^ m * laurentEval (spectralUnit hq0 (1 - s)) a.
```

## The construction

The core is `continuedForms_of_laws`. It works over a general topological
field `F` with a measurable structure. Besides the hypotheses of the target,
it takes four inputs:

- `hμ`: right translation on `LeftUnipotentQuotient n F` preserves `μ`.
- `habv`: every `abv (det g)` is an integer power `q ^ m`.
- `htrans`: right translates `Φg x = Φ (x g)` of row Schwartz–Bruhat
  functions exist.
- `hequiv`: the Fourier equivariance law with the factor
  `(abv (det g))⁻¹`.

Let `M`, `M'` be the original coefficient models and `S` the row
Schwartz–Bruhat space, as in the statement. Set `hq0 : 0 < q` from `1 < q`.

1. **Original family.** `Cf := equalRankContinuationFamily hq hA`. This is the
   trilinear map `M → M' → S → RationalFunctions` sending each triple to the
   unique rational continuation of its original integral. By
   `equalRankContinuationFamily_spec`, each value lies in
   `equalRankRationalValues` (`mem_zetaSpan`). Then
   `IsNormalizedGenerator.clearsDenominators` gives, for every triple, a Laurent
   polynomial `a` with `laurentToRatFunc a = P * Cf f f' Φ`.
2. **Original lift.** `L := laurentLift P Cf hC : M → M' → S → LaurentCoefficients`.
   It is characterized by `laurentToRatFunc (L f f' Φ) = P * Cf f f' Φ`. By the
   helper module, it is trilinear because `laurentToRatFunc` is injective and
   `Cf` is trilinear. Evaluation is never used for this.
3. **Dual family.** `Cfd := equalRankContinuationFamily hq hAd` is the
   continuation family of the dual data
   `(ψ.scale (-1), inverseTransposePullback π, inverseTransposePullback σ,
   firstDualFunctional ψ π ℓ, secondDualFunctional ψ σ ℓ')`. It lives on the
   dual coefficient models. It is pulled back to the original spaces as
   `Cd := trilinearPrecomp Cfd (firstDualModelMap ψ π ℓ)
   (secondDualModelMap ψ σ ℓ') (rowFourierMap hF)`. Thus
   `Cd f f' Φ = Cfd (f̃) (f̃') (Φ^)`. By `dualEqualRankModelIntegral_eq`, this is
   the continuation, in its own variable `t`, of
   `t ↦ dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' (Φ^) t`. So it lies in
   `dualEqualRankRationalValues`, and `Pdual` clears its denominators.
4. **Dual lift.** `Ld := laurentLift Pdual Cd hCd`, with
   `laurentToRatFunc (Ld f f' Φ) = Pdual * Cfd (f̃) (f̃') (Φ^)`.
5. **Forms.** For every `s : ℂ`,

   ```text
   B s     := trilinearPostcomp (laurentEval (spectralUnit hq0 s)) L
   Bdual s := trilinearPostcomp (laurentEval (spectralUnit hq0 (1 - s))) Ld.
   ```

   These are genuine curried complex-linear maps `M →ₗ M' →ₗ S →ₗ ℂ`, being
   compositions of linear maps. After this step only the characterizing
   properties of `L` and `Ld` are used (`clear_value`).

### Evaluation at every parameter

`spectralUnit hq0 s` is the unit `q^(-s)`, which is nonzero because `q > 0`.
Evaluating a Laurent polynomial at a nonzero point is always defined, so
`B s` and `Bdual s` are defined for every `s`. This includes poles of
individual continuations and zeros of `P(q^(-s))` or `Pdual(q^(-(1-s)))`.
Totalized evaluation `RatFunc.eval` at a pole is never used to define a form.

### Regular-point identities with separate guards

Let `Φ, Φhat` be a row Fourier pair and `R`, `Rd` continuations of the
original integral of `(f, f', Φ)` and the dual integral of `(f, f', Φhat)`.

- **Original identity.** By `equalRankContinuationFamily_eq` (uniqueness of
  rational continuation), `Cf f f' Φ = R`, so
  `laurentToRatFunc (L f f' Φ) = P * R`. Assume
  `R.denom.eval (q^(-s)) ≠ 0`. The bridge
  `laurentEval_eq_of_laurentToRatFunc_eq` at `x = spectralUnit hq0 s` then
  gives `B s f f' Φ = P(q^(-s)) * RatFunc.eval (q^(-s)) R`. The bridge's
  guard concerns `R` alone. It needs nothing about `Rd`, and nothing about
  `P` being nonzero at the point.
- **Dual identity.** Since Fourier partners are unique (`eq_rowFourierMap`),
  `Φhat = rowFourierMap hF Φ`. So `Rd` continues the dual integral of
  `(f̃, f̃', Φ^)`, and uniqueness gives `Cfd (f̃) (f̃') (Φ^) = Rd`. Assume
  `Rd.denom.eval (q^(-(1-s))) ≠ 0`. The bridge at
  `x = spectralUnit hq0 (1 - s)` then gives
  `Bdual s f f' Φ = Pdual(q^(-(1-s))) * RatFunc.eval (q^(-(1-s))) Rd`. The
  only guard is on `Rd` at the reflected point. `Rd` itself is a function of
  its own unreflected variable `t`, and the formula evaluates it at
  `t = 1 - s`.

The two identities are proved as separate conjuncts.

### Original translation calculation

Let `g` have `abv (det g) = q^m` and let `Φg x = Φ (x g)`. In the
continuation family, `equalRankContinuationFamily_translate` gives

```text
Cf (g·f) (g·f') Φg = X^m * Cf f f' Φ.
```

This rests on the measure-preserving change of variables on the quotient
(`hμ`), on `lastRow (h g) = lastRow h · g` (`lastRow_mul_eq_vecMul`), and on
`|det (h g)|^s = |det h|^s |det g|^s`. On the integrals this is
`Ψ(s; g·W, g·W', Φg) = |det g|^(-s) Ψ(s; W, W', Φ)` with
`|det g|^(-s) = (q^(-s))^m`, i.e. JPSS (2.10.2).

`laurentLift_translate_original` transfers this to the lift:
`L (g·f) (g·f') Φg = T m * L f f' Φ`. Both sides have the same image under
the injective `laurentToRatFunc`, because `laurentToRatFunc (T m) = X^m`.
Evaluating at `q^(-s)` (`laurentEval_spectralUnit_T_mul`) gives the factor
`(q^(-s))^m`. By `determinantWeight_neg_eq_spectralPoint_zpow`, this equals
`determinantWeight abv g (-s) = |det g|^(-s)`. This proves the twisted
invariance of `B s` for every `s`.

### Dual translation calculation

With the same `g`, `m`, `Φg`, `laurentLift_translate_dual` proves

```text
Ld (g·f) (g·f') Φg = (q^m)⁻¹ • (T (-m) * Ld f f' Φ).
```

The calculation, applied to `laurentToRatFunc` of both sides, runs as follows:

1. **Inverse-transpose model action.** `firstDualModelMap_modelRepresentation`
   and its second analogue: the dual of the translate `g·f` is the translate of
   `f̃` by `gᶥ = inverseTranspose g` in the inverse-transpose model.
2. **Fourier matrix change of variables.** Let `Ψ` be the right translate of
   `Φ^` by `gᶥ`; it exists by `htrans`. `rowFourierMap_translate` gives
   `(Φg)^ = (abv (det g))⁻¹ • Ψ = (q^m)⁻¹ • Ψ`. Linearity of `Cfd` in its third
   argument extracts the scalar.
3. **Reciprocal determinant.** By `abv_det_inverseTranspose`,
   `abv (det gᶥ) = q^(-m)`. The translation law of the dual family at `gᶥ`
   then gives
   `Cfd (gᶥ·f̃) (gᶥ·f̃') Ψ = X^(-m) * Cfd (f̃) (f̃') (Φ^)`.

The combined factor is `(q^m)⁻¹ X^(-m)`, so the lifts differ by
`(q^m)⁻¹ T(-m)`. On integrals this is

```text
Ψ(t; (g·W)~, (g·W')~, (Φg)^) = |det g|^(-1) |det g|^t Ψ(t; W̃, W̃', Φ^)
                             = |det g|^(t-1) Ψ(t; W̃, W̃', Φ^).
```

Evaluating at `t = 1 - s`, i.e. at `q^(-(1-s))`
(`laurentEval_spectralUnit_dual_factor`, using `dual_spectral_factor`), gives
`(q^m)⁻¹ (q^(-(1-s)))^(-m) = (q^(-s))^m = |det g|^(-s)`. So `Bdual s` has
exactly the same twisted invariance as `B s`, at every `s`.

## P-adic instantiation

The final theorem unfolds the statement and installs the same field,
uniform-space and Borel instances by `let`. It then applies
`continuedForms_of_laws` with `q = T.residueCardinality` (and
`T.residueCardinality_gt_one`) and `abv = normalizedAbsoluteValue T`. The
remaining inputs come from:

- `hμ`: `IsCompatible.right_invariant` of the supplied compatible measure `μ`.
- `habv`: `normalizedAbsoluteValue_det_eq_zpow` gives
  `normalizedAbsoluteValue T (det g) = q ^ (-T.ord (det g))`, from
  `normalizedAbs_of_ne_zero`. So `m = -T.ord (det g)`.
- `htrans` and `hequiv`: `padic_row_translate_exists` and
  `padic_rowFourier_equivariance` read the two halves of the published theorem
  `HarmonicAnalysis.padicRowFourierEquivariance F T (n + 1)` in the instance
  context of the statement.
- `padic_row_instances`: in that context, the row space is a Borel space
  (second countability) and every scalar additive Haar measure is
  sigma-finite (sigma-compactness). These instances are needed for
  `rowFourierMap`.

## Relation with JPSS §2.10

Source: H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin–Selberg
Convolutions*, Amer. J. Math. 105 (1983); registered source
`jpss-1983-rankin-selberg`. I read printed p.396 (one-based PDF page 31)
visually.

In §2.10 (proof of Theorem 2.7(iii), second step, case `r = t`), the
integral (2.10.1) is translated. (2.10.2) states
`Ψ(s, π(g)W, π'(g)W', ρ(g)Φ) = |det g|^(-s) Ψ(s, W, W', Φ)` when `s` is not
a pole. The identity `(ρ(g)Φ)^ = |det g|^(-1) ρ(gᶥ)Φ^` is then said to lead
to (2.10.3). The scan prints (2.10.3) as

```text
Ψ(1 - s, (π(g)W)~, (π'(g)W')~, (ρ(g)Φ)^) = |det g|^(-s) Ψ(s, W̃, W̃', Φ^),
```

with `1 - s` on the left but `s` in the integral on the right. The dual
translation calculation above shows that the factor `|det g|^(-s)` relates the
dual integrals at the same reflected parameter `1 - s` on both sides. So the
printed `s` on the right should be read as `1 - s`. The target statement and
this proof use that derived reading throughout: the dual integral is
continued in its own variable `t` and evaluated at `t = 1 - s`. This is an
interpretation of the displayed calculation, not a claim that the scan prints
it.

The normalization is derived as well. Theorem 2.7(ii) (printed p.391) says
the integrals span a fractional ideal with generator `1/P(q^(-s))`, `P(0) = 1`,
and similarly for the inverse-transpose pair. Hence `P * R` and `Pdual * Rd`
are Laurent polynomials in `X = q^(-s)`. JPSS consider the two families of
integrals away from their poles. Here they are multiplied by the scalars
`P(q^(-s))` and `Pdual(q^(-(1-s)))`, which do not depend on the test triple,
and evaluated as Laurent polynomials. This preserves the determinant twist and
gives forms at every `s`. The absence of an exceptional set here is separate
from the finitely many exceptional values of `q^(-s)` in the uniqueness
Proposition of §2.10, which this proof neither uses nor proves. The source
works over arbitrary non-Archimedean local fields; the theorem here is stated
for the Library's `PadicField` scope, while `continuedForms_of_laws` itself
holds over a general topological field under its explicit laws.

## Declarations

- Row Fourier map: `rowFourierMap`, `isRowFourierPair_rowFourierMap`,
  `eq_rowFourierMap`, `rowFourierMap_translate`.
- Determinants and spectral factors: `det_inverseTranspose`,
  `abv_det_inverseTranspose`, `dual_spectral_factor`,
  `laurentEval_spectralUnit_T_mul`, `laurentEval_spectralUnit_dual_factor`.
- P-adic glue: `normalizedAbsoluteValue_det_eq_zpow`,
  `padic_rowFourier_equivariance`, `padic_row_translate_exists`,
  `padic_row_instances`.
- Assembly: `laurentLift_translate_original`, `laurentLift_translate_dual`,
  `continuedForms_of_laws`, and the main theorem `equalRankContinuedForms`.

No `sorry`, `admit` or new axiom is used. The main theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.
