# Rational factorization from the solvable torus quotient

This is a derived adapter between existing Library results. It retains the
explicit structural premise `SolvableTorusQuotientStatement.{u}`; it does not
prove the unconditional `SolvableUnipotentFactorizationStatement.{u}` target.
No original literature assertion or new structural hypothesis is introduced.
The provenance is the imported Library declarations named below.

`subgroupMultiplicationFactors` works over any scheme `S : Scheme.{u}`.
For group scheme maps `a : U ⟶ B` and `t : T ⟶ B`, assume that the actual
scheme morphism `subgroupMultiplication a t` is an isomorphism. Given any
test scheme `V` over `S` and any `b : V ⟶ B.X`, this definition composes `b`
with the inverse of the isomorphism and projects to its two factors. It
returns an ordered pair in `(V ⟶ U.X) × (V ⟶ T.X)`.

`subgroupMultiplicationFactors_spec` uses evaluation by
`comp_subgroupMultiplication_eq` and the inverse identity to show that
these constructed factors satisfy
`(v ≫ a.hom.hom) * (s ≫ t.hom.hom) = b`.
`exists_factorization_of_isIso_subgroupMultiplication` packages this as an
existential statement. The argument uses actual scheme morphisms and
preserves the order of the two factors.

`solvableUnipotentFactorization_of_semidirect` applies that construction to
`SolvableMaximalTorusSemidirectStatement.{u}`. For the arbitrary maximal
torus supplied by the caller, it keeps the same closed, smooth, connected,
unipotent subgroup and its normality on every test scheme. Evaluating the
multiplication isomorphism at `Spec k` gives the required factorization of
all rational points. The stronger input also asserts containment of every
unipotent closed subgroup, which the factorization target does not require.

`solvableUnipotentFactorization_of_solvableTorusQuotient` composes this
adapter with
`solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient`. Its
section input is supplied by
`solvableSplitExtension_of_oneDimensional
perfectFieldOneDimensionalUnipotent`, both already in the Library. Thus its
only remaining structural premise is the exact
`SolvableTorusQuotientStatement.{u}`. In particular, it keeps the arbitrary
universe `u`, every caller-supplied maximal torus, and all original
geometric and group-scheme predicates. The exact target statement and its
imports are unchanged.
