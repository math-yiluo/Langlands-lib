# Conjugation on the original unramified integral image

This internal construction uses the actual nonarchimedean local field `F`,
the inertia fixed field `inertiaFixedField F`, its actual valuation ring
`fixedFieldIntegers F`, and a supplied integral model `M` with its original
generic identification. It constructs the coefficient action on the integral
image of `M.baseChangeUnramified`. Reductivity and smoothness are not needed
for this step.

The integer range consists exactly of the elements whose `fixedFieldValuation`
is at most one. The published equality
`fixedFieldValuation_eq_spectralValuation` and Mathlib's
`spectralNorm_eq_of_equiv` show that every `F`-algebra automorphism of the
inertia fixed field preserves and reflects this range.
`mem_baseChangeUnramified_integralPoints_rationalConjugate_iff` then applies
the existing coordinate criterion to the actual original-model image.

`unramifiedIntegralPointAction` restricts the existing `rationalConjugate`
automorphism to that image, using `baseChangeIntegralPointAut`. Its identity
and composition laws follow from `rationalConjugate_one` and
`rationalConjugate_mul`. The coercion theorem identifies this restriction
with the existing coefficient conjugation on the existing rational-point
carrier. No identification of different integer-ring algebra instances is
used.

The final two lemmas concern a supplied
`MaximalUnramified.BuildingData` and its actual reduced quotient with its
existing rational-point action. A supplied self-map of that quotient must
satisfy the displayed semilinear compatibility with `rationalConjugate`.
Given a point fixed by the original extended integral image, the inverse
of the constructed integral-point automorphism gives a preimage for each
integral group element. Compatibility therefore shows that the mapped
point is fixed by the same image. If its fixed locus is the supplied
singleton, the self-map fixes that point.

These are derived constructions from the published valuation, coefficient
automorphism and original-model base-change machinery. They make no new
original-literature claim. They do not construct an upstairs building,
its semilinear quotient maps or its unique fixed point, and do not show
that an invariant upstairs point lies in a downstairs building image.
The special-vertex, original-image stabilizer, metric and descent
obligations of `BuildingComparisonStatement` remain.
