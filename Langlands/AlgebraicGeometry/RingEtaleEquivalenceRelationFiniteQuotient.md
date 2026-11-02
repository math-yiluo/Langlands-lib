# Finite projective ring relations on finite closed orbit quotients

This internal assembly combines the actual quotient relation with the finite closed orbit ideal. Its rings lie in one arbitrary universe. The original source is the supplied algebra map s, and t is the original target map.

For any ideal I for which B/I is Artinian, `quotientSource_finite_projective` proves that C/s(I) is finite and projective over B/I for the canonical source quotient algebra. The source quotient map is étale by the quotient relation helper. The existing Artinian algebra lemma therefore applies. No equality of source and target extended ideals is required for this source conclusion.

If additionally s(I) = t(I), `quotientTarget_finite_projective` gives the same finiteness and projectivity for the scalar structure induced by the actual target quotient map. This scalar structure is explicit in the statement. It follows from étaleness of that quotient map and the same Artinian algebra lemma. These finiteness conclusions require neither reducedness nor properness of I.

For a Noetherian B and an explicitly supplied nonempty closed subset S with equal source and target prime-spectrum inverse images, the earlier `finiteOrbitIdeal` chooses a proper radical invariant ideal I inside that subset in the sense that its zero locus is contained in S. Its actual quotient B/I is nontrivial, reduced and Artinian. The definition `finiteOrbitQuotientTarget` is exactly the target map for this ideal, using the previously proved equality of its two extended ideals.

The theorem `finiteOrbitQuotient_relation` supplies the unchanged ring étale equivalence relation on B/I and C/s(I). The final two lemmas instantiate the Artinian source and target finite/projective results at this chosen ideal, retaining the two respective scalar structures.

Worker 122 implemented this assembly from the internal finite algebra, finite orbit and actual quotient relation helpers. The finite orbit construction incorporates the topology and ideal work of Workers 101 and 239. The module constructs no restricted coaction and claims no affine quotient, descent conclusion, or nonzero invariant theorem. The nonempty closed invariant subset is an explicit input.
