# Pushforward through countably many measurable branches

`CountableBranchPushforwardStatement`, proved by `countableBranchPushforward`,
applies to a measurable map with a countable measurable cover of its domain.
On each patch the map is a measurable embedding, and it pushes the restricted
source measure to the target measure restricted to the patch image. The
pushforward of the entire source measure has density given by the extended
cardinality of the fibers.

Disjointify the cover by removing earlier patches from each patch. Injectivity
within the original patch identifies the new piece with the preimage of its
own image inside that patch. Hence the local pushforward identity restricts to
the new pieces. For each target point, the fiber is in bijection with the pieces
whose images contain it. Summing the restricted target measures therefore gives
the claimed density. The constant positive finite multiplicity case gives
the corresponding scalar multiple of the target measure on the image.
If the source is Lindelöf with measurable open sets, the latter formula also
applies when each source point has an open patch with the same branch
conditions. A countable subcover supplies the sequence of patches.

This derived measure lemma isolates the passage from local change of variables
to the finite multiplicity factor of the Weyl integration formulas in
Henniart–Lemaire (2011), II.2.10.
