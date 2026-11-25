# Henselian unitary depths from coherent algebraic coordinates

This internal bridge proves
`AlgebraicRankOneIndivisibleLiftsReductionStatement` at every universe `u`.
The statement is the implication from
`AlgebraicRankOneCoordinatesExistenceStatement` to the unchanged published
`QuasiSplitIndivisibleDerivativeLiftsStatement`. Algebraic coordinate existence
remains an explicit premise.

For a smooth affine group with a split subtorus and actual opposite factor
pairs, `mem_indivisibleRoots_of_double_mem` proves that every relative root
whose double is a root belongs to `RelativeRoot.indivisibleRoots`. If
`a = m • b` with `m > 1`, its double is `(2*m) • b`. The integral coroot
bound for actual opposite pairs forces `2*m` to be one or two, a
contradiction. This uses divisibility within the actual root set.

`AlgebraicSU3RootCoordinates.exists_unitaryTowerDepths` works over an
arbitrary field with an integer valuation and a henselian valuation ring.
It retains a supplied actual apartment with full centralizer compatibility,
connected reductivity, maximal splitness, root membership, a torus
centralizer, coherent algebraic SU3 coordinates, and actual normalizer
membership of the Weyl image. The split torus and centralizer have affine
underlying schemes. It applies `coordinateOrigin_depths` to the published
henselian separable extension valuation, using its norm calibration and
invariance under the quadratic involution. The positive coordinates,
packaged without changing their fields or maps, then have exactly
`SU3Root.towerDepth` at the constructed point of the supplied apartment.
This local bridge does not require surjectivity of the base valuation.

The global theorem
`quasiSplitMultipliableUnitaryTowerDepths_of_algebraicRankOneCoordinates`
uses the exact field, valuation, group, torus, apartment and compatibility
inputs of `QuasiSplitMultipliableUnitaryTowerDepthsStatement`. Published
quasi-split torus-centralizer existence and maximal split torus conjugacy
show that the supplied actual centralizer is a torus. Its underlying group
and both maps are retained in `CentralizerDatum.asTorus`. Affineness follows
from splitness and the actual closed centralizer inclusion. Published
rank-one factorization supplies opposite pairs and hence indivisibility of
every multipliable root. The SU3 branch of the supplied algebraic existence
premise now supplies the coherent coordinates and their Weyl normalization.
The local henselian bridge discharges the depth interface separately for
each such root.

Finally `algebraicRankOneIndivisibleLiftsReduction` composes this depth
existence implication with the actual-group lift reduction. Its conclusion
retains every full derivative, including multipliable derivatives, and
every full-V6 compatible apartment in the published target. No field or
residue characteristic or residue-perfection restriction is added.

The provenance is internal composition of the named published root,
centralizer and henselian valuation results with the separate
coherent coordinate and apartment-depth constructions. No new
literature-level assertion is claimed. This module does not prove the
algebraic coordinate-existence premise and therefore does not complete the
unconditional host proof. It uses no local anisotropic classification or
local Kneser–Tits input.
