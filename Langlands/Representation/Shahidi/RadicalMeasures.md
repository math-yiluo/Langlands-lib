# Radical measures in the equal-rank normalization

This derived prerequisite translates items 6 and 7 on printed page 77 of
Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)* (1984). It uses the radical matrices of pages 71–72
and the right translation preceding equation (1.1) on page 78.
The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

The source fixes an arbitrary measure on V and uses that same measure
for both translated Jacquet functionals. It defines the measure on U
by du = da under u(a) = [[I,a],[0,I]], where da is the matrix measure
already fixed in item 5. This is the equal-rank setting. In that setting
U' = U, so the intertwining integral also uses that prescribed matrix
measure. This unit does not extend the seven-item recipe to unequal ranks.

`upperCoordinates` and `lowerCoordinates` extract the actual upper-right
and lower-left blocks of a general linear matrix. The corresponding
identities on `upper` and `lower` follow from the published entry formulas.
`intertwiningUnipotent_equalRanks` proves that the exchanged upper radical
has the original coordinate map when the ranks agree; the type-level rank
cast acts identically on each index.

`upperRadicalMeasure`, `lowerRadicalMeasure` and
`intertwiningRadicalMeasure` push a supplied rectangular measure through
the published concrete radical maps. Their outputs are measures on the
ambient general linear group obtained from radical coordinates, not
assertions of Haar invariance on that ambient group. Actual coordinate
extraction recovers the original measure under the stated Borel and
topological-ring hypotheses. The proofs compose measure pushforwards
and use the block extraction identities. Consequently each upper and
lower transport is injective on measures. This also prevents a loss of
normalization information through a nonmeasurable map in those results.

`IsEqualRankRadicalMeasureCompatible` takes matrix measures da, μA,
μJ, μJ' and ambient measures du, dv. It asserts four explicit equations:
du is the upper transport of da and the exchanged upper transport of μA,
while dv is the lower transport of both μJ and μJ'. Here μA is the
intertwining coordinate measure and μJ, μJ' are the measures used for the
two functionals after the page 78 translation to the common V coordinates.
Under the Borel hypotheses, `coordinate_eq` proves μA = da and μJ = μJ';
the final equivalence includes the two ambient pushforward equations.
Its forward proof uses injectivity, and the reverse proof substitutes
the coordinate equalities.

The relation does not impose Haar, nonzero, regularity or self-duality
conditions, nor choose the arbitrary V measure. In particular the matrix
measure da is not assumed self-dual (compare printed page 82). Such
hypotheses and the item 5 coordinate compatibility belong to the full
suitable-measure system. This unit does not assert the existence or
stabilization of a Jacquet functional, prove the change of variables
between its integral formulations, or state Theorem 5.1. The rectangular
transport constructions also make sense in rank zero, while the cited
representation-theoretic application has positive equal ranks.
