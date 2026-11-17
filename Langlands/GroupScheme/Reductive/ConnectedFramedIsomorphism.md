# Torus and Borel isomorphisms from coherent actual root frames

This internal assembly constructs global isomorphisms of reductive groups with
supplied closed split fibrewise maximal tori. It assumes full global coordinate
root data on both original groups, coherent frames of their actual root modules
on all affine tests, the affine pinned isomorphism theorem, and étale-local
isomorphism of the groups. Affineness of their structure morphisms is available
from reductivity. It imposes no affineness condition on the base scheme.

`basedIsoOfEtaleLocalIsoOfCoherentFrames` first uses étale-local group
isomorphism to identify the full root data and corrects the identification to
carry the two supplied bases onto each other. It inverts this full equivalence
to match the character-pullback convention of the pinned comparison theorem.
Global pinned descent then gives an actual `BasedCoordinateIso`, retaining
both full lattices and their central torus directions.

`torusIsoOfEtaleLocalIsoOfCoherentFrames` chooses arbitrary bases of the two
finite reduced integral root data and takes the resulting torus-preserving
isomorphism. The base scheme need only be nonempty once the full coordinate
data and coherent root frames are supplied. No Borel input is required.

For a connected base and supplied relative Borels containing the two tori,
`torusBorelIsoOfEtaleLocalIsoOfCoherentFrames` instead chooses bases whose
canonical positive-coroot cocharacters present those original Borels. The
global based-coordinate isomorphism respects the canonical cocharacters.
The actual representative-transport theorem therefore gives both the torus
and Borel range equalities on every test scheme, recorded by `TorusBorelIsoData`.

The construction is conditional on coherent actual root frames and the affine
pinned theorem. Their existence from the actual line-bundle Picard hypothesis
and the proof of the affine theorem remain separate prerequisites. This pair
does not claim the unchanged parent's unconditional theorem.
