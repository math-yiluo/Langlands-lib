# Completeness of positive-polyradius restricted power series

Author: Worker 228.

The theorem `Langlands.Analytic.GeneralizedTateAlgebra.completeness` proves
the entire published proposition `CompletenessStatement r K`, imported
unchanged from
`Langlands.Geometry.Analytic.GeneralizedTateAlgebra.CompletenessStatement`.
Its hypotheses are exactly those of the target. These are an arbitrary
variable type `σ`, a positive real polyradius `r`, and a normed commutative
ring `K` with an ultrametric distance and `CompleteSpace K`. It is the
instance `instCompleteSpace`, which installs completeness of the actual
`GeneralizedTateAlgebra r K` for the weighted Gauss norm built in
`GeneralizedTateAlgebra.Definitions`.

## Proof

The proof works directly with Cauchy sequences, using
`Metric.complete_of_cauchySeq_tendsto`. It uses only the following facts:

- the norm bound `weighted_norm_coeff_le`;
- the criterion `norm_le_iff`;
- strict positivity of every monomial weight `r.weight d`;
- the cofinite decay that defines membership in the algebra.

1. *Coefficients are Lipschitz.* Dividing `weighted_norm_coeff_le` by the
   positive weight gives `‖coeff d f‖ ≤ ‖f‖ / r.weight d`
   (`norm_coeff_le_div`). The coefficient map `coeffLinearMap r K d` is
   therefore Lipschitz with constant `(r.weight d)⁻¹`
   (`lipschitzWith_coeffLinearMap`), hence uniformly continuous. For a
   Cauchy sequence `u`, each coefficient sequence is therefore Cauchy in `K`
   (`cauchySeq_coeff`). By completeness of `K` it has a limit, and these
   limits form one formal series `F` (`exists_tendsto_coeff_of_cauchySeq`).
2. *Uniform weighted estimates pass to the limit.* Suppose `‖f - u i‖ ≤ ε`
   eventually and `u` converges coefficientwise to `F`. Then
   `‖coeff d (series f - F)‖ * r.weight d ≤ ε` for every `d`, because the
   left side is a limit of quantities bounded by `‖f - u i‖`
   (`weighted_norm_coeff_sub_le_of_tendsto`, by `le_of_tendsto`).
3. *The limit has cofinite weighted decay.* Given `ε > 0`, choose `N` with
   `dist (u m) (u n) < ε / 2` for all `m, n ≥ N`. Step 2 bounds every
   weighted coefficient of `series (u N) - F` by `ε / 2`. The one late term
   `u N` is restricted, so cofinitely its weighted coefficients are below
   `ε / 2`. The triangle inequality in `K` then makes the weighted
   coefficients of `F` cofinitely below `ε` (`isRestricted_of_cauchySeq`).
   Hence `F` defines an element `ofSeries r K F _` of the algebra.
4. *Norm convergence.* For `n ≥ N`, step 2 applied to `u n` bounds every
   weighted coefficient of `u n - ofSeries r K F _` by `ε / 2`. Then
   `norm_le_iff` gives `‖u n - ofSeries r K F _‖ ≤ ε / 2 < ε`
   (`tendsto_ofSeries_of_cauchySeq`).

The argument never chooses a coefficient of prescribed norm, and it never
uses the ultrametric inequality beyond the imported construction of the
algebra. It uses no finiteness or nonemptiness of `σ`, no nontriviality or
field structure on `K`, and no condition relating the radii to a value
group. Empty variable types, the zero coefficient ring, trivially valued
coefficients, and arbitrary strictly positive real radii are all covered.

## Helper declarations

These are exposed for downstream quotient and analytic constructions:

- `series_injective`, `ext_coeff`, and the definitional `series_zero`,
  `series_add`, `series_neg`, `series_sub`, `series_smul`;
- `ofSeries` builds an element from a restricted series, with
  `series_ofSeries`, and `isRestricted_series` states that every element's
  series has cofinite weighted decay;
- `coeffLinearMap r K d`, the `K`-linear coefficient map, with
  `coeffLinearMap_apply`;
- `norm_coeff_le_div`, `lipschitzWith_coeffLinearMap`,
  `uniformContinuous_coeff`, `continuous_coeff`, and
  `tendsto_coeff_of_tendsto`, which says norm convergence along any filter
  gives coefficientwise convergence;
- `cauchySeq_coeff`, `weighted_norm_coeff_sub_le_of_tendsto` (stated for an
  arbitrary nontrivial filter), `isRestricted_of_cauchySeq`,
  `tendsto_ofSeries_of_cauchySeq` and `exists_tendsto_coeff_of_cauchySeq`.

Only the last of these and the instance require `CompleteSpace K`. The
others hold for any ultrametric normed commutative coefficient ring.

## Provenance

For finitely many variables over a complete nonarchimedean field, the
proved property is the completeness assertion of Berkovich, *Non-Archimedean
analytic spaces* (Trieste lectures, 2009), Example 1.2.2(v), page 4, as
cited by the target's Markdown. The broader scope of the variable type and
coefficient ring is the target's own derived extension. The Lean route
follows the suggested coefficientwise-limit argument in the task context
and the target's Markdown. It does not transport through the unit-radius
`StrictTateAlgebra`.
