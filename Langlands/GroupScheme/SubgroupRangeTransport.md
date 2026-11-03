# Range transport through monomorphisms

This internal group-scheme helper is derived directly from the all-test
definition of `SubgroupFunctor.range`, the group laws on morphisms into a group
object, and categorical cancellation by a monomorphism. It introduces no
structural assertion about algebraic groups.

For homomorphisms `i : H ⟶ K` and `j : K ⟶ G` over any scheme `S`,
`rangePostcompHom i j U` sends a point in the range of `i` to its composite
with `j`. When the underlying morphism of schemes over `S` of `j` is monic,
`rangePostcompEquiv i j U` is a multiplicative equivalence between the ranges
of `i` and `i ≫ j` on the test scheme `U`. Its value is specified by
`rangePostcompEquiv_apply_coe`. The construction is surjective because a
point in the composite range already comes from a point of `H`, and
injective by monic cancellation.

The corollary `range_comp_eq_bot_iff` states that the all-test range of
`i ≫ j` is the identity subgroup functor exactly when the range of `i` is
the identity subgroup functor, assuming the same monicity of `j`.
The proof applies cancellation to individual test points and uses preservation
of identity points by group homomorphisms.

All declarations lie in `Langlands.GroupScheme.SubgroupFunctor` and apply
at arbitrary universe `u`. This helper is intended for transporting terminal
vanishing in the dynamic-centralizer reductivity proof; it does not prove
that theorem.
