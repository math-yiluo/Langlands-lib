# Proper parabolic subgroups and solvability

`Langlands.GroupScheme.properParabolicSolvable` proves
[`ProperParabolicSolvableStatement`](ProperParabolicSolvableStatement.md).
The argument follows Milne, *Algebraic Groups* (2017), Corollary 17.17,
printed p. 356, using the Borel containment criterion of Theorem 17.16.

If the ambient group is solvable, `IsParabolicSubgroup.exists_isBorelSubgroup_factor`
realizes the geometric Borel witness over the given algebraically closed
field. Write its inclusion as `b = f ≫ i`, with `i` the parabolic
inclusion. Apply Borel maximality to the identity of the ambient group to
see that `b` is an isomorphism. Then `inv b ≫ f` is a section of `i`.
Since `i` is a closed immersion on underlying schemes, it is monic, so
the section makes it an isomorphism.

For a nonsolvable ambient group, `borelConjugacy` supplies a Borel
inclusion. The map to the base given by the algebraic closure is an
isomorphism on spectra. Thus `IsBorelSubgroup.baseChange_of_isIso` makes
the base-changed inclusion a Borel, and the identity factorization
witnesses parabolicity. If the inclusion were an isomorphism, solvability
of the Borel would imply solvability of the ambient group by
`IsSolvableGroupScheme.of_iso`.
