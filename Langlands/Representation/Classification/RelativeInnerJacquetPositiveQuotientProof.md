# Positive inner Jacquet counts detect inner quotients

`glRelativeInnerJacquetPositiveQuotient` proves the exact Library proposition
`GLRelativeInnerJacquetPositiveQuotientStatement`, with independent field,
fine-carrier and coarse-carrier universes. It characterizes positivity of each
supplied actual inner Jacquet count by existence of an actual inner quotient.

The proof selects a grade equivalent to the test representation from a positive
actual factor count. Its grade projection and the chosen equivalence give a
surjective intertwiner from an actual invariant subspace to the test.

For the inner Jacquet representation, the proof first transports the supplied
actual finite-series count to the flattened product Levi along
`flattenedLeviEquiv`. The double-pullback equivalence identifies the transported
fine test with its literal real determinant twist. The actual pulled Jacquet
representation is admissible by
`Parabolic.flattenedRefinedOppositeJacquetAdmissibility`; the flattened test is
irreducible and Levi-cuspidal by real-twist preservation. Applying
`CuspidalSupport.leviCuspidalConstituent_maps` to the selected actual
subquotient supplies an embedding into that admissible representation. Pulling
the embedding back and using the actual double-pullback equivalence gives a
nonzero map from the fine twist into the original inner Jacquet representation.
Injectivity and nontriviality of the irreducible fine twist prove nonvanishing.

The inner clause of `fineOppositeJacquetQuotientDetection`, supplied with the
two proved clauses of `Parabolic.normalizedSecondAdjointness`, identifies that
nonzero map with an actual quotient of the inner induction. Conversely a
quotient gives a nonzero fine-to-Jacquet map through the same detection clause;
`SimpleMapMultiplicityDetectionProof.positive_of_simple_map` proves positivity
of the supplied actual count.

This is an internal assembly of published actual-series transport, cuspidal
extraction and second-adjointness results. It assumes the actual count witness
specified by the target. It constructs neither count existence nor an ambient
comparison or an irreducible head, and uses no unitarity or genericity.
