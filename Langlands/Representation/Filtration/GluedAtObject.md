# Selected factors of a glued filtration at an object

This internal helper constructs `IsGluedFrom.selectedFiltration` and derives
`IsGluedFrom.exists_selected_filtration` from
the published gluing definition, evaluation construction, and zero-factor
deletion theorem. It does not assert a geometric lemma.

For an actual functor `F` glued from finitely many representation functors,
fix an object `X` and a predicate on the original indices. If every
unselected factor has a subsingleton carrier at `X`, the result constructs
an actual object filtration of `F(X)`. Its steps are indexed by an
enumeration of the selected original indices, and its graded
representations are equivariantly isomorphic to those factors at `X`.
Selected indices are retained even when their factors also vanish.

The proof unpacks the gluing permutation and its natural filtration,
evaluates at `X`, and transports vanishing across each graded natural
isomorphism. It applies `ObjectRepFiltration.zeroFactorDeletionTheorem` to
the predicate composed with the permutation. Restricting the permutation
gives an equivalence back to the selected original indices. Finally it
composes the deletion equivalences with the evaluated graded isomorphisms.
All coefficient, group, carrier, object, and morphism universes remain
independent, as in the imported constructions.

The definition `IsGluedFrom.selectedFiltration` chooses the length,
enumeration, actual filtration, and grade-equivalence witnesses supplied
by this existence theorem. It uses classical choice; no canonical ordering
of the selected indices is asserted.
