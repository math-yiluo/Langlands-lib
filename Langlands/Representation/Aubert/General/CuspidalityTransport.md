# Cuspidality under transport of actual Jacquet test families

This is an internal deduction from the published definitions
`IsCuspidalFor` and `IsLeviCuspidal` in
`Langlands.Representation.Aubert.General.SupportCategory` and the actual
normalized Jacquet comparison `GroupTransport.jacquetIsoApp` in
`Langlands.Representation.Aubert.General.GroupTransport`. It contributes a
transport step to the cuspidal-support association proof. It does not prove
`RationalCuspidalSupportAssociationStatement` or construct a conjugating
normalizer representative.

The ambient groups have universe `uG` and the complex representation carriers
have independent universe `uV`. The two test-index types also have independent
universes. Both groups are locally compact nonarchimedean topological groups.
Each test triple has an actual semidirect decomposition and a closed unipotent
subgroup, as required to define its normalized Jacquet functor. No finite length,
admissibility, compactness of a parabolic quotient or compact-limit assumption
is used.

`jacquet_subsingleton_pullback_iff` uses the actual equivariant isomorphism
`GroupTransport.jacquetIsoApp` to identify the normalized Jacquet module after
pullback with the pullback of the original Jacquet module. Pullback keeps the
underlying vector space. The injectivity of the resulting linear equivalence,
in each direction, transfers the property that the carrier is subsingleton.
The subgroup matching hypotheses concern the Levi and unipotent subgroups.
There is no additional matching premise for the parabolic subgroups.

`IsCuspidalFor.pullback` applies this comparison to each target test. A map from
target tests to source tests suffices for preservation of cuspidality.
`isCuspidalFor_pullback_iff` proves the converse when that map is surjective,
so every source test is also checked. `IsCuspidalFor.of_iso` applies the
Jacquet functor to an actual smooth equivariant isomorphism and transfers
subsingletonness by the resulting linear equivalence.

`isLeviCuspidal_conjugation_iff` specializes the family comparison to the
proper-standard-subset tests that define `IsLeviCuspidal`. Its ambient group
equivalence is the published `conjugationEquiv n hn`, with action
`x ↦ n⁻¹ * x * n`. The same actual `n` occurs in the Levi membership equivalence
`hn` and in every tested Levi and radical membership equivalence. A supplied
bijection matches all proper subsets in the two standard Levi index sets.
Closedness of the two ambient Levis supplies their local compactness instances.
`IsLeviCuspidal.of_iso` specializes preservation by isomorphism to the same
inside-Levi predicate.

`conjugateLeviCuspidalDatum` constructs the actual transported irreducible
cuspidal datum under these same matching hypotheses. Its underlying object
is exactly `(conjugationFunctor n hn).obj σ`, on the original vector space.
Irreducibility is preserved by the published
`Langlands.isIrreducible_comp_continuousMulEquiv_iff`; cuspidality follows from
the preceding family comparison. The construction returns an actual smooth
representation with both proofs, before passage to isomorphism classes.

The proper-subset bijection and the membership equivalences are explicit
hypotheses of this conditional transport lemma. This module makes no claim
that root association alone has already supplied them. Establishing that
structural matching for the actual rational-point families remains a separate
deduction in the association proof.

The proof bodies use the cited Jacquet comparison, the same-carrier
definition of smooth pullback, preservation of irreducibility under group
equivalence, functoriality on isomorphisms and elementary properties of
equivalences. They contain no application of Langlands
classification, character independence, a geometric lemma or adjointness.
Those results are not supplied as new premises or discharged by this helper.
