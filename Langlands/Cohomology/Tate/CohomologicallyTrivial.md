# Cohomologically trivial finite-group representations

`Langlands.Tate.IsCohomologicallyTrivial A` means that the actual Tate
cohomology of the restriction of `A` to every subgroup is zero in every
integer degree. The group is finite, the commutative scalar ring and all
carriers lie in arbitrary `Type u`, and the coefficients are actual
`Rep` objects. The quantifier includes every choice of finite enumeration
of each subgroup.

This is a derived internal predicate packaging the vanishing notion used
in [the existing Tate vanishing statements](CohomologicalTrivialityStatement.md).
Its `IsZero` condition concerns Mathlib's actual `tateCohomology` module
objects; it does not introduce another cohomology theory or assert a
vanishing theorem.
