# Actual normalizer lifts for associated opposite conjugation

This internal adapter works over an arbitrary field with the published actual
simple relative roots and scheme relative Weyl group. It retains explicit
proofs of the all-test standard Levi transport statement and the outer
associated opposite parabolic/radical transport predicate. It proves neither
structural assertion.

`longestSchemeNormalizerLift` chooses a representative of the actual
`longestRep cs J` in `normalizerPoints i`, using surjectivity of the quotient
map. Its quotient class is proved in `longestSchemeNormalizerLift_mk`.
`inversePointNormalizer` embeds the inverse of any such point into the actual
normalizer of the torus point image, using only
`normalizerPoints_le_pointNormalizer`. Its underlying ambient point is
literally the inverse. No equality of normalizer subgroups, comparison of
centralizers or equivalence of the two Weyl quotients is assumed.

For a finite scheme relative Weyl Coxeter system satisfying the existing
`IsRelativeWeylCoxeterRealization`, the theorem
`rootSet_associatedSubset_of_schemeCoxeter` identifies the actual character set
at the associated subset with the inverse longest element's image of the
original character set. The implemented proof uses
`minimalityLengthCriterion_proof` to obtain positivity on the original labels,
then `IsRelativeWeylCoxeterRealization.conj_simple_iff` to convert reflection
conjugation to exact equality of characters. The generic
`associatedSubsetLaws_proof` supplies the required simple reflection images.
The argument distinguishes characters from their negatives and uses the
existing criterion for possibly nonreduced relative roots.

`associatedLevi_map_conj_of_schemeCoxeter` composes the preceding character
image with the longest element and cancels its inverse. It then applies
`levi_map_conj_of_character_image`, whose explicit
`StandardLeviConjugationStatement` premise supplies the all-test Levi
transport. The result is the actual rational-point image
`Int(n)(M_associated) = M_J` for every lift of that longest element.

`associatedOpposite_mem_of_structural` combines this Levi result with
`IsStandardAssociatedOppositeTransport.mem_rationalPoints`. For the same lift
`n`, standard cocharacter `ζ` at `J` and ambient rational point `x`, it gives
the three membership equivalences for the standard groups at the associated
subset and the actual opposite parabolic, standard Levi and opposite radical
at `J`. All use `g = n⁻¹`, so the consumer expression `g⁻¹*x*g` is
`n*x*n⁻¹`. The dynamic `oppositeCocharacter` of the structural predicate and
`inverseCocharacter` defining the consumer's opposite subgroups are
definitionally the same inversion of the multiplicative-group parameter.

Finiteness and the actual Coxeter realization remain inputs; no realization
existence is proved here. The root labels, actual normalizer representatives
and subgroup functors are unchanged. Empty root types, nonsplit connected
reductive groups and positive characteristic are included. This algebraic
adapter introduces no topology or representation carrier restriction.
It establishes no induction-class identity, natural duality or closed
rational contragredient commutation theorem.

The provenance is composition of the named published constructions and
conditional structural interfaces. The point evaluation adapter is due to
Worker 1107; this module specializes it to the actual opposite subgroups and
adds the independently supplied Levi transport. No literature theorem is
newly asserted. The proof bodies invoke no Langlands classification,
character independence, geometric lemma, adjointness or cuspidal-support
theorem.
