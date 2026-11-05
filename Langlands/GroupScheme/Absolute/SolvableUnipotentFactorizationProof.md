# Rational unipotent-times-maximal-torus factorization

`Langlands.GroupScheme.solvableUnipotentFactorization` proves exactly
`Langlands.GroupScheme.SolvableUnipotentFactorizationStatement.{u}` for arbitrary
universe `u`. It has no additional premise. The statement pair and its imports
are unchanged.

For every algebraically closed field `k : Type u`, smooth connected affine
solvable group scheme `B` over `Spec k`, and caller-supplied maximal torus
`t : T.toGrp ⟶ B`, the theorem supplies a smooth connected unipotent group
scheme `U` and a closed subgroup `a : U ⟶ B`. Its range subgroup functor is
normal on every test scheme. Each rational point `b` of `B` admits rational
points `v` of `U` and `s` of `T.toGrp` satisfying
`(v ≫ a.hom.hom) * (s ≫ t.hom.hom) = b`, in that order.

The proof applies the published
`solvableUnipotentFactorization_of_solvableTorusQuotient` from
[`SolvableUnipotentFactorizationOfQuotient`](SolvableUnipotentFactorizationOfQuotient.md)
to the published exact theorem `solvableTorusQuotient` from
[`SolvableTorusQuotientProof`](SolvableTorusQuotientProof.md). This discharges
the adapter's sole structural premise.

The adapter uses
`solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient`, with the
splitting input supplied by
`solvableSplitExtension_of_oneDimensional perfectFieldOneDimensionalUnipotent`.
This yields the actual subgroup multiplication isomorphism for the same maximal
torus supplied by the caller. It also supplies `U`, `a`, their geometric
properties, unipotence, and all-test normality.

To obtain the factors, `subgroupMultiplicationFactors` composes a point with
the inverse of that multiplication morphism and then with the two product
projections. Its proved specification gives the ordered product identity.
`solvableUnipotentFactorization_of_semidirect` specializes this construction
to `Spec k`, the test scheme defining rational points, while retaining the
subgroup properties. The final theorem is the composition of these published
results and adds no structural hypothesis.

This is a derived proof using the Library declarations named above. The
original-source correspondence for its target is recorded in
[`SolvableUnipotentFactorizationStatement`](SolvableUnipotentFactorizationStatement.md).
Its stated conclusion is the ordered rational-point existence assertion.
