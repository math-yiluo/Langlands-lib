# Etale torus conjugacy retaining one integral coordinate matrix

For any actual isomorphism between coordinate split tori over a field, `fieldTorusCoordinateEquiv` constructs the covariant integral character-coordinate equivalence. Its inverse is the ordinary contravariant character pullback. `fieldIsoExtension_eq_coordinateIso` identifies extension of that field torus isomorphism over any base with the actual exponent torus isomorphism of this fixed integral equivalence.

Let any smooth affine group scheme over an arbitrary affine base have two specified fibrewise maximal coordinate split tori. Reductivity, connectedness, a nontrivial base ring and reducedness are not extra hypotheses. `exists_etale_coordinateConjugacy` proves that through every base point there is an affine etale neighborhood on which the two tori are conjugate through one integral coordinate equivalence, with an actual conjugator and an exact equation for the normalized base-changed torus inclusions.

The proof follows the established etale-local maximal-torus conjugacy construction, retaining its coordinate data. On a geometric field fibre, actual maximal-torus conjugacy in the identity component supplies a conjugator and a field torus isomorphism. Extend that isomorphism by its integral coordinate matrix over the original base. The existing identity-transporter lifting theorem supplies an affine etale neighborhood and an actual conjugator satisfying the same fixed torus square. The explicit exponent-isomorphism base-change formula normalizes both pulled-back torus inclusions and proves the desired equation. It does not assert that arbitrary torus isomorphisms over a disconnected base have one constant matrix.

`EtaleCoordinateConjugacyData` records the actual neighborhood ring and projection, etaleness, coverage of the chosen point, the fixed integral equivalence, the conjugator, and the exact square. `etaleCoordinateConjugacyAt` chooses these proved data; existence of the conjugator or a constant coordinate map is not a premise.

This unit gives a local existence theorem and data. It does not combine the neighborhoods into a finite cover, apply the construction inside a specified parabolic, compare base-changed filtration terms, or perform global descent.

Provenance: internal strengthening of the published etale-local maximal-torus conjugacy construction, preserving the fixed integral coordinates already used by its field-extension and transporter-lifting proof.
