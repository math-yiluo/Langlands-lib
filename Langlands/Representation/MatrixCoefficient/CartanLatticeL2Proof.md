# L2 assembly from finite translated lattice cells

Author: Worker 19.

`cartanLatticeL2` proves `CartanLatticeL2Statement` with independent universes
for the group, representation carrier and finite coordinate type.

For each lattice index, form the union over the finite middle translating
set of the images of the corresponding double cosets in the full central
quotient. Quotient induction and the supplied Cartan cover show that these
sets cover the quotient: the last central factor maps to the identity.

Finite subadditivity bounds each union's measure by the cardinality of the
middle set times the supplied common cell-volume bound. The resulting real
volume constant is nonnegative. Neither disjointness nor measurability of
the individual cells is needed for this upper estimate.

For every vector and smooth functional, use the supplied radii and coefficient
constant. On the image of a double coset, the descended norm equals the norm
of the original coefficient. Its real absolute value is the same norm, so
the original estimate bounds the function used by the analytic L2 theorem.
Smoothness, contained in admissibility, gives almost everywhere strong
measurability through `aestronglyMeasurable_coefficientNorm`.

Apply the published `finiteLatticeCellL2` with polynomial degree zero.
The coordinate radii and cell-volume weights are the same as the supplied
ones, so every strict squared-coefficient/volume gap is retained. The result
is the required `MemLp` assertion for each input pair and hence
`IsSquareIntegrableModCenter`, using the original central character.

This is an internal finite-union and integration argument. It assumes the
displayed cover and estimates and proves no geometric or spectral existence
result. Empty coordinate types and empty middle sets are covered by the same
finite-sum argument. It introduces no finite-length or irreducibility
hypothesis and uses no classification, geometric lemma, adjointness,
character independence or cuspidal-support result.
