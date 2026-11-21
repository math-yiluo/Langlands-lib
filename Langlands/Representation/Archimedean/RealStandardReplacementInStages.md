# Split real Fourier replacements in stages

`SplitFourierReplacement` records a forward map, a compact-equivariant
right inverse, and the natural-number Fourier weights of the forward
map at pairwise disjoint rotation slots. The forward map intertwines
the real Lie action. The compact Fourier determinacy theorem gives
compact equivariance of the forward map. The Library's
`RealTemperedForm.chain` supplies these data for the character
replacement of a standard parameter.

`SplitFourierReplacement.inStages` constructs both ambient maps by
induction in stages. The slice formula preserves the right inverse
identity, and the coefficient theorem transports the multiplier to
the shifted slots. `compDisjoint` assembles two such replacements in
disjoint coordinates. The new weights are the product of the two
weights, and the right inverse is the reverse-order composition of
the two lifts.

`RealStandardReplacementInStagesStatement` identifies the two ambient
maps with the corresponding induced local maps.

This is an internal construction from the Library's Fourier replacement
and normalized slice formulas. It provides the actual lift for the
compact duality pairing assembled from local inducing factors.
