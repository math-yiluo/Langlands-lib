# Topology and Haar measures on actual central quotients

Author: Worker 158.

`Langlands.CentralQuotientHaarTopology G` is a proposition about the actual
quotient `G / Subgroup.center G`, with its quotient topology. It asserts that
this quotient is a Hausdorff, locally compact, second-countable topological
group. For every measurable space equal to its Borel sigma algebra, the
quotient admits a Haar measure and every Haar measure is sigma-finite.
Neither a normalization nor a particular measurable-space instance is fixed.

`Langlands.GLBlockCentralQuotientTopologyStatement` asserts these properties
for every `GeneralLinear n F.Carrier` and every actual product Levi
`B.Levi F.Carrier`. It quantifies every prime, every finite p-adic extension in
an arbitrary universe, every supplied compatible `TopologicalData`, every rank
including zero, and every block shape. The field and Levi topologies are
exactly those supplied by `T`. The quotient uses the full group center, not
an ambient scalar subgroup. No representation carrier occurs in the statement.

This is an internal topology prerequisite for the block-tensor analytic
comparison. The proposed derivation reuses the published GL second-countability
result `TopologicalData.generalLinearSecondCountableTopology`, finite-product
second countability, and the published topological-group, Hausdorffness and
local-compactness results in `Group/GL/Padic` and `Group/GL/PadicBlocks`.
A topological group's quotient map is open; its quotient by the closed center
therefore inherits local compactness, second countability and Hausdorffness.
Mathlib supplies Haar existence and sigma-finiteness on these locally compact,
second-countable groups. These files define the propositions only; the proof
is a separate successor.

The statement does not identify the Levi quotient with a product of factor
quotients, compare Haar normalizations, factor smooth duals, or establish
integrability. Those remain separate obligations of the analytic comparison.
