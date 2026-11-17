# Full based coordinate root-data comparison

This internal construction corrects an equivalence of full coordinate root
data to carry any supplied simple-root base onto another supplied base.
It retains the entire character and cocharacter lattices, including all central
directions.

Actual realization of a coordinate datum over a field embeds its Weyl group
by conjugation into that of its realized datum. The latter has finite image
in the actual normalizer action of the closed split torus, so it is finite.
For a global coordinate datum over a nonempty scheme, realization on one
residue fibre supplies the same finiteness.

The positive-coroot sums of the two supplied bases are regular integral
coweights. The published chamber-alignment theorem gives a Weyl correction
matching their root signs under the original equivalence. The published
positive-indecomposability criterion then shows that the corrected full
equivalence carries the two simple-root supports onto each other.

`basedGlobalCoordinateRootDatumEquivOfEtaleLocalIso` applies this correction
to the full equivalence produced by an étale-local group isomorphism. Its
inputs are reductive groups over a nonempty scheme, supplied split fibrewise
maximal tori, closedness of the target torus, finite reduced global coordinate
data and their bases, and the étale-local group isomorphism. Connectedness is
not required once the global coordinate data are supplied. The output is an
actual full root-datum equivalence together with its simple-support equation;
this construction does not itself lift it to a group isomorphism.
