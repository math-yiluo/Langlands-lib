# Local coordinate isogeny conjugacy without supplied root data

This internal derived module removes the supplied fibrewise root data from
the preceding local isogeny adapter. The intrinsic proposition
`AffineSplitSurjectionRootDatumStatement` remains an explicit hypothesis of
the proved implication.

`LocalCoordinateIsogenyTorusConjugacyStatement` is the existence assertion
over every commutative local ring R. The actual groups G and H are reductive,
and their coordinate split tori are closed and maximal on every residue-field
fibre. The actual ambient homomorphisms phi and Phi are finite, flat and
surjective isogenies. The restriction of phi to the source torus factors
through the target torus, and both restrictions agree.

The conclusion is the existing `FppfLocallyTorusConjugate` predicate: an actual
fppf cover of Spec R and a target torus point on each cover member whose
conjugation identity holds on every further scheme test and every
source-group point. No fibrewise root data, root-weight trivializations,
root-datum isogeny or torus character formula is a premise of this local
coordinate assertion.

`localCoordinateIsogenyTorusConjugacy_of_affineSplitSurjectionRootDatum`
proves the assertion under the explicit intrinsic proposition. Reductivity
supplies the affine structure morphisms. Published
`localSplitFibrewiseRootDatumExistence` constructs the two finite reduced
fibrewise coordinate root data. Their finiteness and reducedness are extracted
from `IsFibrewiseRootDatumOf`. The isogeny hypotheses supply finiteness of both
ambient maps and surjectivity of the first. Convert the supplied group-scheme
torus homomorphism to the additive notation for commutative-group-scheme
morphisms; equality of restrictions gives the same square for Phi. The
preceding local root-datum adapter now yields the conclusion.

The provenance is direct composition of the published local root-datum
existence theorem, the definitions of reductivity and isogeny, and the
conditional local adapter. This module neither proves the intrinsic
proposition nor extends local-ring existence to arbitrary bases. Local
spectra alone do not supply an fppf cover of an arbitrary affine scheme, so
the unconditional general-base rigidity theorem remains a separate goal.
