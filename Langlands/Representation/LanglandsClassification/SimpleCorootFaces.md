# Simple-coroot faces and the standard index

This internal construction records the final index-recovery step used in
Renard VII.4.2(ii), after equality of the full dominant parameters is known.
It uses the actual simple relative roots, the supplied integral coroot data
and the full real character space of the torus, including central directions.

`simpleCorootZeroIndex` is the subset of simple relative roots whose coroot
evaluations vanish at a full real character.
`openSimpleCorootFace` requires zero coroot evaluations on a specified index
and strict positivity on its complement among the simple roots. These are
precisely the zero and positivity conditions inside the published
`restrictedCorootChamber`.

For indices contained in the simple roots,
`eq_simpleCorootZeroIndex_of_mem_openFace` recovers the index from any full
character in its face. Inclusion in the zero index follows from vanishing;
the reverse inclusion follows because a complementary simple-root coroot
has strictly positive evaluation. Consequently,
`index_eq_of_equal_openFace_lifts` proves that two such faces containing
equal full characters have equal indices.

Conversely, a character with nonnegative evaluations at all simple coroots
belongs to the face of its zero index: a nonnegative evaluation that is
nonzero is strictly positive. `existsUnique_openFace_of_dominant` combines
this fact with index recovery to obtain a unique index for every dominant
full character. No finiteness, regularity or nonempty-root hypothesis is
needed.

`restrictedCorootChamber_eq_image_openFace` identifies the published chamber
of a split component with the image of the full face under its actual
character restriction map. The proof rearranges the existential lift and
the two conditions in the unchanged chamber definition.

This is an internal consequence of those definitions, motivated by the
common-parameter step of Renard, *Représentations des groupes réductifs
p-adiques*, 2026 version, VII.4.2(ii), printed pp.245–246 / PDF pp.251–252.
The implemented argument recovers the index from simple-coroot zero
evaluations. It does not assert the stronger structural or spectral
assertions used earlier in Renard's proof.

In particular, equality after restriction to split components is not
equality of full lifts. This module proves neither that two triplets with
a common quotient have equal full lifts, nor the Langlands combinatorial
decomposition V.3.18, nor the representation-isomorphism or exhaustion
parts of classification.
