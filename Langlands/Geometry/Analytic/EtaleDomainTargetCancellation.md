# Étale cancellation along analytic domain inclusions

Let `K` be a complete ultrametric normed field. If the composite of a
localized analytic map with the canonical inclusion of its target domain
is étale, `etale_of_comp_domainι` proves that the original map is étale.
Field universe `u` is independent of the common space and chart-index
universe `v`. The target can be any analytic domain.

For a strong map, the proof pulls each open ambient target neighborhood
back to the domain. A recognized affinoid piece of the domain has an
actual recognized image in the ambient target. The inverse image of
that chart is the same source piece because the inclusion is injective.
The bounded coefficient map is the composite of the ambient pullback
with the constructed equivalence of the target affinoid algebras. This
preserves Banach finiteness and étaleness at the same source point.
The joint pointwise criterion recovers the all-pieces étale certificate.
For a localized map, a right fraction reduces the argument to its
numerator by the étale invariance under isomorphisms.

The definition `etaleDomainLift` certifies the existing unique domain
lift when the image of an étale map lies in a domain. It retains the
factorization equation with the canonical inclusion.

This internal construction uses the recognized image and bounded
equivalence from `DomainEmbeddingRecognition`, the joint all-pieces
criterion from `FullRecognitionAllPiecesRestriction`, and the
strong and localized étale comparison. The algebra comparison uses
the complete bounded pullback map.
