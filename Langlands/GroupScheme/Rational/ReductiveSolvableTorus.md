# Solvable connected reductive groups are tori

Over an arbitrary field, a group scheme that is connected reductive and
geometrically solvable is a torus. The theorem
`IsConnectedReductive.isTorus_of_isSolvableGroupScheme` retains both predicates
as defined in the Library and makes no perfectness or characteristic
assumption.

The proof passes to the chosen algebraic closure. Smoothness, affineness and
connectedness persist, and the geometric unipotent-radical hypothesis is
exactly the required triviality of the unipotent radical there. Solvability
persists by the equivalence with uniform all-test solvability for smooth
affine groups and preservation of that bound by base change. Apply the
proved `algClosedReductiveNormalSolvableTorus` to the identity inclusion of
the entire base-changed group as a smooth connected solvable normal closed
subgroup of itself. The resulting torus property descends by
`IsTorus.of_baseChange`.

`IsConnectedReductive.torusOfIsSolvable` equips the original group scheme
with the commutative structure supplied by this torus property. Its
underlying group scheme is definitionally the original one, and
`isTorus_torusOfIsSolvable` records its torus property over the original
field.

This is an internal consequence of the named published theorem and the
Library's base-change and solvability constructions. It does not assert
that a particular centralizer is reductive or solvable; those geometric
properties remain separate obligations in the quasi-split centralizer
problem.
