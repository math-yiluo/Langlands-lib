# Restriction and finite affine refinement of permutation atlases

This internal derived module compares original-group coordinates of normalized
restricted charts with the original chart coordinates. It uses that comparison
to transport local permutation equations under restriction of chart bases.

`coordinates_restrictChart` follows from the base-change point inverse law and
`restrictChart_coordinates`. `AgreeBy.of_coordinates` is the converse direction
of the original-coordinate agreement criterion. `LocallyPermutes.restrict`
pulls the chosen overlap neighbourhood back along the actual map of overlaps,
lifts the new open into the old open, and compares original-group coordinates on
every relative test. The coordinate equivalence is retained on the pulled-back
open. The chart restriction maps are arbitrary; no open immersion assumption is
imposed on them.

`HasEtalePermutationAtlas.exists_finiteAffine` assumes only compactness of the
base in addition to the supplied small étale permutation atlas. Étale maps are
open, so the published quasi-compact-cover refinement theorem gives a finite
affine étale cover mapping to the old atlas. The normalized restricted charts
and `LocallyPermutes.restrict` retain the actual group-scheme chart data and the
local permutation equations. Finite coordinate types are pulled from their
parent cover members, retaining varying and empty ranks.

The construction is in every universe, with no affineness or nonemptiness
hypothesis on the group scheme. It does not construct the final Weil comparison
or assert the unchanged relative-Borel presentation theorem.

`FiniteAffinePermutationAtlas` packages the actual finite affine étale cover,
its finite index proof, varying finite coordinate types, actual normalized split
charts and local all-test permutation equations. The noncomputable construction
`HasEtalePermutationAtlas.finiteAffine` chooses the refinement established by
`exists_finiteAffine`, retaining all those data rather than only their existence.
