# Actual finite neighborhood data for the canonical small second projection

This internal assembly constructs the local finite target data and
pointwise etale pieces for the existing canonical small second projection.
The field and space/index universes are independent. Quotient smallness
and an existing local product index are explicit. All geometric inputs
come from a genuine finite first neighborhood inside open Hausdorff
factor and common-base patches; global ambient separation is not assumed.

For every point of the right open patch, the proved image-controlled
neighborhood construction gives finitely many recognized right affinoids
through that point. Each entire image lies in one recognized base chart
inside the original finite target neighborhood, and their union is an
ambient neighborhood. The original first finite-over data supplies its
whole left preimage over each such base chart. The actual single-pair
construction recognizes each entire simultaneous preimage in the canonical
small product. The existing full-recognition second-projection pullbacks
on these pieces are finite Banach by their complete coefficient identities
and finite bounded pushout base change.

The target pieces are actual recognized whole original charts of the
selected right atlas. Their literal loci agree with the original right
recognized affinoids, so the finite family retains its point membership,
open-patch containment and ambient neighborhood union. The small source
neighborhood is the simultaneous inverse image of the original left open
neighborhood and the right open patch. Every constructed piece is exactly
its entire preimage in this source neighborhood.

`smallFiniteTargetFamily` proves all this actual local finite data. The
further theorem `smallSnd_isFiniteOver` applies the general
`FiniteOverTargetLocalityStatement`, supplied explicitly as an input, to
obtain finiteness over the two open neighborhoods. This module does not
prove that general criterion, recognition over arbitrary target affinoids
independently of it, or effective finite algebra descent.

For a genuine all-pieces etale first neighborhood and a corresponding
actual small quotient point, the constructed family also gives
`HasFinitePiecesAt` for pointwise etaleness of the existing second
projection. The quotient base-map equation identifies the two original
base images. The original all-pieces certificate applies to each whole
left preimage at the actual first image of the same quotient point. Full
tensor base change transfers this certificate to the actual second
pullback. The definition tests every recognized preimage with the specified
locus. Such a recognized object is a propositional subtype of its literal
set, so locus equality identifies it with the constructed preimage by two
applications of subtype extensionality. No algebra-map equality is inferred
from point actions.

The provenance is internal: image-controlled finite recognized
neighborhoods, genuine finite product neighborhoods, actual entire
single-pair preimages, complete canonical small-projection coefficients,
and finite Banach/tensor base change. The general target-local criterion
and algebraic comparison statements are explicit inputs to the relevant
conclusions. Upgrading finite pieces to all pieces, global etaleness of
the second projection, and the final localized pullback theorem remain
separate obligations.
