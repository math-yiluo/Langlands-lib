# Pointwise étaleness of recognized inverse images

This internal construction uses the actual bounded pushout comparison from
`RecognizedContainedMap` and the pointwise tensor base-change theorem from
`AffinoidPointwiseBaseChange`. The recognized subsets and their literal
inverse-image equality are supplied, as are the finite Banach pushout and
finite tensor comparison propositions. It does not prove the unrestricted
pointwise lifting statement.

`recognizedPullbackPoint` pulls a point of the unchanged recognized source algebra
back along `fullRecognitionPullbackEquiv` to the actual affinoid pushout algebra.
The first pushout projection has the same ambient source point: the comparison
preserves the structural bounded map from the original source chart, and the
recognized contained restriction induces the ambient inclusion.

`fullRecognitionPairs_isEtaleAtPoint_of_pushout` assumes that the original bounded
map is finite Banach and is étale at that projected point. The supplied finite
tensor comparison transfers pointwise étaleness to the second pushout leg.
The bounded equivalence is algebraically finite étale, so composition transfers
étaleness to the recognized source point. Finite Banach base change supplies
finite type for the second leg, as needed for composition of pointwise
unramifiedness. The identity of entire bounded maps identifies this composite
with the full-recognition map.

For a source chart and a target chart whose ranges are the entire ambient spaces,
`isEtaleAtAllPieces_of_globalCharts` transfers any supplied open locus of pointwise
étaleness of the original finite Banach map to étaleness over all pieces. Global
finiteness comes from `RecognizedFinitePullback`. For every recognized inverse
image and every point over the chosen ambient point, the chart identity above
places its actual pushout projection in the supplied locus. The pointwise
transfer then gives both unramifiedness and flatness in the definition of
`HasAllPiecesAt`, with the full ambient spaces as finite neighborhoods.
The open locus supplies the outer neighborhood in `IsEtaleAtAllPieces`.
`isEtaleAllPieces_of_globalCharts` applies this with the entire source when the
original map is étale at every spectrum point. Both finite base-change
propositions remain explicit hypotheses; openness of a pointwise étale locus is
not established here.
