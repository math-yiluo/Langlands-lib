# Positive forms on an actual irreducible operator realization

This internal prerequisite for actual cuspidal multiplicity one compares two supplied
positive invariant forms on the same actual operator realization. The field is an arbitrary
number field in any universe, the rank is any natural number, and the realization is
irreducible and jointly admissible for the actual finite adelic and standard infinite
compact actions. Both supplied forms are also skew for every genuine real Lie direction.

`OperatorUnitaryFormComparisonStatement` asserts that the second form is a positive real
scalar multiple of the first on every pair of actual vectors. The module proves this
statement with `operatorUnitaryFormComparison`; `UnitaryForm.exists_pos_scalar` exposes
the same conclusion on a supplied realization.

The proof uses the actual pointwise-conjugate realization and the published joint-dual
Riesz representation theorem. Each supplied form gives a specified perfect bilinear
pairing with that conjugate realization. Identifying the two images in the joint dual
produces a linear automorphism of the conjugate realization. The published comparison
laws for invariant pairings show that it commutes with finite translations, compact
translations and the real Lie action. The published enveloping comparison extends this
to the entire differential action, hence to every actual operator. The published
countable-dimension Schur theorem makes this automorphism a complex scalar. The
compatibility equation for the two specified pairings gives the scalar identity of
forms. Evaluating on a nonzero vector shows that the scalar is real and strictly positive.

The provenance is internal composition of `UnitaryContragredientCriterion`,
`CuspidalConjugateRealization`, `ContragredientUniqueness` and
`IrreducibleCentralCharacterProof`. No new external theorem or existence of a form is
asserted. Joint admissibility remains an explicit hypothesis here; the published
`CuspidalOperatorRealization.isJointlyAdmissible` supplies it for cuspidal inputs.

This result compares algebraic positive forms. It does not construct a full archimedean
Hilbert action, identify Hilbert smooth vectors with actual functions, bound a Whittaker
functional in the smooth Hilbert topology, or prove Whittaker uniqueness or the
unconditional cuspidal operator multiplicity-one target.
