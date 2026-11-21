# Reflection of étaleness on affine analytification charts

The theorem `isEtale_of_localizedHom_etale` converts localized étaleness of an
actual affine analytification into the finite-pieces étale predicate on its
strong representative. The field and the two coefficient algebras can lie in
independent universes. This conversion is an internal consequence of the
Library's definitions of saturation, full recognition, and localized étaleness.

Localized étaleness makes the canonical strong extension to the double
saturations étale over all recognized pieces. At a point in the source, the
proof chooses a finite neighborhood for this extension inside a first-saturation
chart interior. It intersects the target neighborhood with a first-saturation
chart interior and restricts the source by inverse image. Étaleness over all
pieces gives a finite étale pullback over each recognized target subset of the
restricted neighborhood.

A recognized subset contained in a first-saturation chart is the range of a
first-saturation chart by local-domain completeness. This applies to each
target subset and to its recognized inverse image in the restricted source.
The construction `liftedRecognitionIndexOfSubset` chooses a first-saturation
index lifting the given double-saturation recognized subset. It first views
the recognized subset as a domain of the containing chart, then takes a
first-saturation representative of the resulting chart. Injectivity of chart
ranges proves the equality of recognized subsets. For these pieces, the
original restriction formula conjugates the full-recognition bounded map by
bounded equivalences with the chart algebras. Both directions of each
equivalence are finite Banach and algebraically finite étale. The saturation
extension agrees with the first-saturation pullback on the lifted charts, so
the two finiteness properties descend to the first-saturation pieces.

For affine analytification, the radius-\(m\) chart lies in the interior of the
radius-\(m+1\) chart. Every point lies in some radius chart, so the preceding
local construction gives the required finite étale neighborhoods everywhere.
The pointwise criterion then gives the finite-pieces étale predicate.
