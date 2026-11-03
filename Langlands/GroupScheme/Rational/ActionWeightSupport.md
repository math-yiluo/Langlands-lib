# Semigroup action support and positive relative-root indexing

This internal helper derives the action support needed for the ordered-root
product assembly from the published definitions. It works over any field and at
every universe, for an affine group scheme acted on by a commutative group
scheme. It introduces no external structural assertion.

The imported `actionWeightSupport_mono` from `Rational.SemigroupClosure`
keeps the same nonzero tangent vector and weight
membership while enlarging its subgroup. For the whole subgroup the tangent
membership condition is automatic. The support therefore consists exactly of
the characters with a nonzero action weight space, including the zero character
when its weight space is nonzero.

`actionWeightSupport_eq_inter_of_hasLieImage` assumes both an exact Lie image
equal to `semigroupWeightSpan b A` and that the subgroup's support lies in `A`.
The forward inclusion is support monotonicity. For the reverse inclusion a
nonzero ambient vector of weight in `A` lies in the corresponding summand of
the semigroup weight span, so the exact Lie-image hypothesis puts its actual
dual-number point in the subgroup. No assertion about independence of distinct
weight spaces is needed.

`actionWeightSupport_semigroupSubgroup` is conditional on the full
`SemigroupRealizationStatement`. Its maximality clause applied to the generated
subgroup itself supplies the support bound; its Lie-image clause supplies the
other hypothesis. This proves that the complete support is ambient support
intersected with the chosen semigroup.

For conjugation, `actionWeightSpace_conjugation` identifies the intrinsic and
adjoint weight spaces. A character with positive pairing is nonzero. Thus the
intersection of ambient support with `positiveSemigroup` is exactly
`positiveRelativeRoots`, even for a zero or nongeneric cocharacter.
`actionWeightSupport_positiveSemigroup` specializes the preceding conditional
identity. `positiveSemigroupRootEquiv` is the resulting equivalence of indexing
types and preserves the underlying character.

This module proves no semigroup realization theorem, Dynamic comparison,
root-ray decomposition, or ordered-product theorem. Its realization assumption
must be discharged before using it in the unconditional task target.
