# Actual root support at a rational chamber wall

This internal prerequisite for Task 5515 converts a finite rational chamber wall
into actual root calculations in any supplied representative of its dynamic
centralizer. It uses the original split torus and its actual character lattice;
that torus need not be maximal in the ambient group. Throughout, the base is a
field and the ambient group `G` is affine.

`IsWallDirection i x y w` records regular endpoints, a nonempty vanishing root
set at `w`, opposite endpoint signs on that set, agreement with the wall signs
on every remaining root, and proportional vanishing root evaluation forms.
The published finite-arrangement `WallAdjacent` witness supplies precisely
these conditions, together with its protected nonvanishing forms. Swapping the
endpoints preserves the conditions. When `G` is smooth and connected and `A`
is split, the nonnegative support implication proves that both actual endpoint
parabolics lie in the wall parabolic. Smoothness and connectedness are additional
ambient hypotheses, not consequences of `IsWallDirection`.

Let `r` be any positive integral realization of `w`, and let `j : M → G` be
any representative of its dynamic centralizer, with a compatible factor `iM`
of the original torus. For this root comparison, both `G` and `M` are assumed
affine and locally of finite type over the field. The actual roots in `M` are
exactly the ambient roots
vanishing on `w`. One direction uses root containment under a monomorphism and
centrality of the defining cocharacter in its centralizer; the other uses the
published differential identification of wall-orthogonal weight spaces.
Evaluating proportional rational root forms on two integral cocharacters then
proves `HasProportionalRootPairings iM` on the original torus.

When `M` is connected reductive and the original torus is split, opposite
endpoint signs on those roots identify the second inner dynamic parabolic with
the parabolic of the negative first endpoint realization. This follows from
the published actual-root parabolic containment criterion in both directions.
The first inner parabolic is proper: fullness would make its cocharacter
central by reductivity, hence force zero pairing on every actual root, in
contradiction with endpoint regularity and a root vanishing on the wall.

All results are derived from imported published structural results and rational
arithmetic. This module does not supply actual maps retaining a specified Levi,
construct rank-one wall data, or prove the gallery existence propositions.

Integral directions use the existing `rationalCocharacterEvaluation` and
`rationalCocharacterEvaluation_toRat` from `RelativeReflectionPairing`, matching
the consolidated `RationalCocharacterRealization` interface.
