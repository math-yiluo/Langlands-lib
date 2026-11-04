# Actual cuspidal transport from root association

This internal construction transports the actual inside-Levi cuspidality
predicate and actual irreducible cuspidal data along a supplied root-association
representative. It is a prerequisite for cuspidal-support association; it does
not establish existence of an association witness or an isomorphism between
two independently supplied data.

Let `i : T → G` be a monomorphic torus map over an arbitrary field `k`, with
affine `G`, generic cocharacter `ν`, connected reductive `G`, maximal split
`T`, finite simple-root type, and the point-normalizer and point-centralizer
comparisons `hN`, `hZ`. Assume `StandardCocharacterStatement`. Fix finite
simple-root subsets `I`, `J`, a rational point `n`, and a witness of
`rootAssociation i ν hN hZ I J n`. Throughout, the same rational point `n`
acts on the actual group and representation carriers.

The theorem `rootAssociation_restrictedParabolic_unipotent_mem` matches
the standard parabolic and unipotent tests for every finite descendant
`K : Finset I`, after sending `K` through `rootAssociationFinsetEquiv`.
Its membership equivalences are restricted to actual `x ∈ M_J`; the
transported point is `n⁻¹ * x * n`. This restriction is essential.

The proof applies the published
`mem_standardParabolic_unipotent_inv_conj_iff_of_character_images`.
Finiteness follows from the finite simple-root type. Descendant inclusion
follows from `leviIndex_subset`. The assumed standard-cocharacter statement
provides cocharacters for both parent faces. The parent and descendant
character-image equalities come from `rootAssociation_character_image` and
`rootAssociation_leviIndex`. Evaluating on the rational-point test scheme
keeps the original normalizer representative.

For the cuspidality result, give the rational-point group a locally compact
nonarchimedean group topology, assume closedness of all standard unipotent
subgroups and of the two parent Levis, and assume
`StandardLeviIntersectionStatement`. The latter supplies the exact
inside-Levi semidirect decompositions already used by `IsLeviCuspidal`.
The representation carrier universe `v` is independent of the field and
ambient group universe `u`.

The theorem `isLeviCuspidal_rootAssociation_conjugation_iff` states that
the actual inverse-conjugation pullback of `σ` is cuspidal in `M_J` if and
only if `σ` is cuspidal in `M_I`. Its proof applies the generic
`isCuspidalFor_pullback_iff` to the actual continuous equivalence
`rootAssociationLeviEquiv` and the inverse of
`rootAssociationProperFinsetEquiv`. Descendant-Levi membership and the
restricted unipotent membership theorem give the required matching.
Surjectivity of the proper-subset equivalence gives both implications.
No global ambient unipotent-matching hypothesis is added.

The definition `rootAssociationConjugateCuspidalDatum` returns the actual
object `(conjugationFunctor n hn).obj σ`, paired with its irreducibility
and inside-Levi cuspidality proofs, where `hn` is
`rootAssociation_levi_mem`. Irreducibility is preserved by the published
continuous-group-equivalence pullback theorem; cuspidality uses the
preceding equivalence.

The preliminary general lemma
`Langlands.SmoothRep.isIrreducible_pullbackFunctor_obj_iff` packages the
published irreducibility comparison for the actual smooth pullback functor.
Its two topological group universes and its representation carrier universe
are independent. Naming this comparison before specializing to rational
points keeps the kernel's definitional comparisons small.

All results are derived from the named published structural and Jacquet
transport interfaces. No new literature assertion is introduced. There is
no finite-length, admissibility, endpoint, or quotient-compactness
hypothesis. Existence and comparison of actual cuspidal support data remain
separate obligations.
