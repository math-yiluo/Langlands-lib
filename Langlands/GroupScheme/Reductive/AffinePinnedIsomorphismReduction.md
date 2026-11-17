# Affine pinned full faithfulness from unpinned existence

Worker 243, with Worker 163 supplying affine pinned uniqueness.

`affinePinnedIsomorphismTheorem_of_unpinned` derives the unchanged `AffinePinnedIsomorphismTheoremStatement.{u}` from the explicit premise `AffineSplitIsomorphismTheoremStatement.{u}`. It applies the pinning-correction construction of `AffinePinnedExistenceReduction` to obtain an isomorphism with the full torus-character and pinning predicate. The uniqueness theorem of `AffinePinnedUniqueness` proves that every other isomorphism with this same predicate equals the constructed one. All the target's original universal quantifiers and hypotheses are retained, including arbitrary commutative rings and the zero ring.

`uniqueAffinePinnedIsomorphismOfUnpinned` packages this result as a `Unique` structure on the subtype of actual group isomorphisms satisfying the full target predicate. Its default is the constructed actual isomorphism; its uniqueness field follows from the compiled full theorem.

The unpinned existence premise is not discharged by this conditional reduction. The unconditional exact proof must supply it from a separately accepted and published proof. This module supplies no replacement definition of either published target.

The mathematical route is Conrad, *Reductive group schemes* (2014), Theorem 6.1.17, p.197: existence is corrected using the quotient-torus argument of Corollary 6.1.15, while uniqueness is Proposition 6.1.13(2), pp.194–196. The implemented arbitrary-ring existence and uniqueness proofs are documented in their respective imported modules.
