# Finite relative dimensions on the actual target point space

Author: Worker 109. This derived supporting construction combines the published
scheme smooth-dimension, actual local fibre-dimension, etale chart comparison,
and quotient point-topology results. It supplies the numerical geometric step
needed to handle varying dimensions in the adelic smooth-openness proof.
No new external assertion is assumed.

For two commuting etale chart squares of the same space morphism, form their
represented source and target overlaps. Etale source maps preserve the actual
local topological dimension of residue fibres. Etale target maps are locally
quasi-finite and likewise preserve that dimension. The two comparison equations
therefore show equality of local dimensions on the source overlap.
Equality of quotient chart points has a point in that represented overlap, so
the local dimension depends only on the actual source point.

For a smooth scheme chart with locally Noetherian source, each actual source
component is open and connected. The published
`smoothConnectedRelativeDimension` chooses its natural-number smooth dimension.
The published `smoothPureDimension` identifies that dimension with pure
dimension of the actual residue fibres, and the existing local-dimension
comparison identifies its value at every source point. The resulting
`sourcePointDimension` is locally constant on the component opens.

A surjective etale source chart induces the quotient point topology.
`EtaleMorphismChart.pointDimension` chooses a preimage in this atlas.
The overlap argument proves that every other commuting etale chart computes the
same actual local fibre dimension. It also proves that pulling this function
back to its original atlas recovers the selected component dimension.
Consequently it is locally constant, and its range is finite when the atlas
source is compact.

The module proves that a smooth morphism is open on the ordinary quotient point
topologies: its source atlas is surjective, its scheme chart map is smooth and
open, and its target etale chart maps open sets to open sets. This statement
concerns the scheme point topology.

If geometric fibres are connected and nonempty, every locally constant
natural-number function on source points is constant on the fibres of the
quotient point map. Represent the common target image by a field-valued point.
The existing point-pullback lifting theorem lifts both source points to its
actual presheaf fibre. The fibre projection is continuous, so the pulled-back
locally constant function is constant by connectedness.

`smoothTargetPointDimensions` applies these results over an affine locally
Noetherian base to finite-presentation compact atlases and a quasi-separated
target. A published common-chart theorem supplies affine source and target
charts; structural local finite presentation makes the source locally
Noetherian. A smooth surjection with nonempty geometrically connected fibres
therefore has a finite-range locally constant dimension function on its actual
target point space. Pulling back along every etale chart square computes that
chart's actual local fibre dimension. Surjectivity is an explicit input here
and is already available for the adelic stage models.

The dimension fibres of this function are clopen point subsets. Constructing
the associated open algebraic subspaces, proving fixed chart smoothness of
their restrictions, applying uniform Lang-Weil and assembling the adelic
topologies remain separate obligations. This unit does not assert the final
adelic openness theorem.
