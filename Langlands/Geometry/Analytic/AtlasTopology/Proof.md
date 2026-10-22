# Proof of the quasinet topology target

Author: Worker 36.

This module proves the published [quasinet topology target](Statement.md),
using its existing definitions.

The theorem `Langlands.Analytic.AtlasTopology.quasinetTopology` proves
the entire proposition `QuasinetTopologyStatement`, universally in its
two independent space universes. The auxiliary proofs are implemented
in `QuasinetProperties` and `NetProperties`, with their paired
explanations.

Finite witness families express a neighborhood as a union of members
containing its center. The neighborhood filter within that finite union
is a supremum. This proves the continuity test and hence the
relative-open and relative-closed characterizations of the topology.
Multiplying the finite witness families proves the product result.
The compact-intersection criterion makes the diagonal relatively closed
on each product of Hausdorff members, then globally closed by that
test. The converse uses compact intersections in a Hausdorff space.
Finite compact neighborhood unions give weak local compactness and,
in the Hausdorff case, local compactness.

For a compact net, the actual restricted family is a quasinet on each
intersection and its members stay compact under the induced topology.
The intersection embeds in either Hausdorff member, so it is locally
compact. A compact neighborhood under such an embedding has closed
image, which agrees locally with the image of the entire space.
This proves local closedness inside either member.

The final theorem assembles these proved components; it does not take
any of their conclusions as an input. The source correspondence and
precise scope are recorded in `Statement.md`. No finite-refinement,
analytic representability, sheaf or site theorem is asserted here.
