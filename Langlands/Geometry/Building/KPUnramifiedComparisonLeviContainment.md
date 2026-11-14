# Centralizer containment for integral descended vectors

For a supplied concrete unramified apartment lift and any integral downstairs
cocharacter, this lemma puts every extended downstairs centralizer point in the
upstairs pairing Levi for the image of that cocharacter in the real upstairs
cocharacter space.

The chosen upstairs cocharacter is the base change of the downstairs
cocharacter followed by the supplied torus map. Naturality of scalar extension
and `CentralizerDatum.isRepresentedBy_baseChange` show that an extended
downstairs centralizer point centralizes this cocharacter. The derived lemma
`dynamicCentralizer_rationalPoints_le_of_zeroRootGroups` then applies: the
pairing Levi contains the full upstairs torus centralizer and every root group
with zero cocharacter pairing. The identification of integral and real zero
pairings is `RealTorusSpace.eval_tmul`.

This is an internal consequence of the cited Library results supporting the
Levi field in KP sections 9.6 and 9.8.2; it uses no comparison field as a premise.
