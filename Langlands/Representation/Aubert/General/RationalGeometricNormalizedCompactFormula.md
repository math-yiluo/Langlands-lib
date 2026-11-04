# Original-function formulas for the actual normalized compact comparison

This internal deduction makes the canonical-measure evaluation of
`geometricNormalizedCompactEquiv` explicit on the class of each original compact
function. It keeps the original target inverse half-character, the actual
compatible quotient integral and the class-preserving source Jacquet map.
The full rational geometric exact-K0 expansion remains open.

The original subgroups, structural data, measures and character conventions are
those of `RationalGeometricNormalizedCompact` and
`RationalGeometricCompactAnalysis`. No independently chosen Haar or quotient
measure, character-balance premise or orbit-comparison assertion is introduced.

`geometricCompactEquivOfCompactLimit_eval_mk_integral` specializes the existing
`geometricCompactEquiv_eval_mk_integral` to the Borel Haar measures
`geometricCompactKernelHaar`, `geometricCompactIntersectionHaar`, and the selected
`geometricCompactQuotientMeasure`. Their right invariance, compatibility and the
compact open subgroup bases are the already proved actual-group results.

`geometricNormalizedCompactCoefficientEquiv_apply` identifies the linear map
underlying the normalized coefficient equivalence with
`geometricInducingHalfJacquetEquiv`. Surjectivity of the original Jacquet class
map reduces this to their identical original-vector formulas.

`geometricNormalizedCompactEquiv_eval_mk_integral` evaluates the full normalized
comparison on the class of an original compact function F, at each original
target Levi point l. Its value is kappa(l) times the source Jacquet comparison
applied to the actual quotient integral of `geometricCompactIntegrand` for
`twist chi sigma`. Here chi is the original U_J positive half-character and
kappa is the original U_I inverse half-character. The proof uses the evaluation
formulas for compact induction of a coefficient equivalence and compact
induction of a character twist, linearity of the coefficient equivalence, and
the canonical-measure evaluation theorem above.

`geometricCompactIntegrand_finMeasSupp` proves finite measurable support of
the existing actual quotient integrand for every quotient measure finite on
compact sets. It uses the finite measurable support of
`quotientCoinvariantSimple` and the fact that the linear coefficient map
preserves zero.

`geometricNormalizedCompactIntegrand` maps that actual simple function through
`geometricInducingHalfJacquetEquiv` into the ordinary original source Jacquet
carrier. For every original kernel point q, its value on the quotient class of
q is exactly the ordinary class `Jacquet.mk sigma S (F(q * s(l)))`.
Here q is included through the original intermediate subgroup into P_I and
s is the original inclusion of M_I into P_I. The source radical is the literal
subgroupOf copy of M_J intersect n⁻¹ U_I n in M_J. The representative formula
follows from `geometricCompactIntegrand_mk` and the class-preserving
`geometricInducingHalfJacquetEquiv_mk`; the finite measurable support law again
follows because this linear map preserves zero.

`geometricNormalizedCompactEquiv_eval_mk` gives the resulting formula with the
source Jacquet comparison moved inside the integral:

```
normalizedComparison([F])(l)
  = kappa(l) • integral geometricCompactQuotientMeasure
      geometricNormalizedCompactIntegrand(F,l).
```

The measure here is exactly the canonical compatible quotient measure already
used by the compact comparison. Its finiteness on compact sets follows from
compatibility with the actual right-invariant intersection Haar measure.
`AlgebraicIntegral.integral_linearMap`, with the proved finite measurable
support, commutes the source Jacquet linear map through this integral. The
pointwise integrand has no extra scalar: the original inducing half remains
in the transformation law of F, while the target inverse half remains as the
displayed factor kappa(l). This formula does not identify the remaining
coefficient character with the normalized geometric-term character.

The field and coefficient-carrier universes are independent. These declarations
use the original connected reductive group, maximal split torus, generic
cocharacter, arbitrary standard indices and torus-normalizer point, and original
source/target semidirect decompositions. They retain ambient local compactness,
Hausdorffness and nonarchimedean structure, closedness of the displayed original
radicals, parabolics and Levis, continuity of the original Levi projections and
the compact-limit property of U_I at their respective declaration scopes.

This is an internal consequence of the named comparison and integral
definitions. The proof bodies add no geometric expansion, adjointness, cuspidal
support, character independence or Langlands classification input. The imported
module closure is larger. Distinct-radical balance on the whole common Levi,
identification with the normalized geometric term, compact/full induction,
ordered filtration and the final exact-K0 sum remain separate obligations.
