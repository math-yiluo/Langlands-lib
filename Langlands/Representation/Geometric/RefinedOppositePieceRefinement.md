# Whole-piece comparison for the chosen geometric-lemma refinement

This internal construction removes the prescribed source-refinement
requirement from `reversedWholeLeviGeometricPieceEquiv`. The source refinement
`S'` may be any refinement whose actual refined Levi equals the source Levi
intersection of `reversedPiecePermutation B S C x`. This is the form supplied
by the existential refinement in the normalized geometric lemma.

The input permutation `x` conjugates the actual Levi of `B.flatten S` onto
the actual Levi of `C`. The constructed reversed permutation therefore
conjugates the flattened reversed refinement onto `C.reverse`. The published
whole-piece intersection calculation identifies its source Levi with the
refined Levi of `reverseRefinement B S`.

The helper module `RefinementUniqueness` proves that equal actual standard
refined Levi subgroups determine equal refinements. Applying that theorem
to the two descriptions of the source intersection gives
`S' = reverseRefinement B S`. Equality elimination then permits the existing
`reversedWholeLeviGeometricPieceEquiv` construction to apply.

The resulting representation equivalence compares the chosen upper
geometric piece pulled back by `leviReverseEquiv C` with Weyl transport by
`x` of the original inner normalized opposite Jacquet module, in flattened
fine-Levi coordinates. The field and representation-carrier universes are
independent. The coarse representation is any actual smooth representation;
minimality, cuspidality and irreducibility are not required.

This is a derived comparison of actual representations. It does not assert
the existence of a geometric filtration, occurrence as a grade or
subquotient, a multiplicity comparison, branch selection, continuation or
the supported obstruction theorem. Its provenance is the actual
intersection and transport calculations named above, together with the
algebraic and finite-order uniqueness proof documented in the paired helper
Markdown.
