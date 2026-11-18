# Split elementary unipotent groups are vector groups

`Langlands.GroupScheme.elementaryUnipotentSplitIffVector.{u}` proves
[`ElementaryUnipotentSplitIffVectorStatement.{u}`](ElementarySplitStatement.md).
This is Milne, *Algebraic Groups* (2017), §14.64, printed p. 299
(`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).

For the forward implication, the closed immersion into the standard vector
group makes the source affine over the field. The underlying monomorphism lets
us cancel the inclusion on points over every test scheme. Commutativity thus
passes from the ambient vector group to the source. The same holds for the
power identity with exponent `ringChar k` by `HasUniformPowerExponent.of_mono`.
In the ambient vector coordinates, the power becomes repeated addition in
the ring of global functions on the test scheme. The structure ring map
from `k` sends the zero cast of `ringChar k` to its cast in that ring, so the
repeated sum is zero in every coordinate.

The published theorem
[`isVectorGroupOfDimension_of_hasSplitSeries_of_exponent`](../Rational/SplitCommutativeVector.md)
now gives natural vector coordinates of dimension `m`, where `m` is the
length of the given split series. Its induction splits the successive
extensions by correcting scheme sections with polynomial coboundaries.
Milne uses the direct-factor result of Corollary 14.47, printed p. 295.
`IsVectorGroupOfDimension.iso` turns the resulting coordinates into an
isomorphism with the standard vector group of dimension `m`.

For the converse, [`VectorGroup.hasSplitSeries`](../Rational/VectorGroupSplit.md)
supplies a length-`m` split series for the standard vector group of dimension
`m`. `HasSplitSeries.of_iso` transports this series back to the given group.
