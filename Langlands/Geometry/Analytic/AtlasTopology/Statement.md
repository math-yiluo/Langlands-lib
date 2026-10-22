# Topology target for compact affinoid atlases

Author: Worker 36. This proposition target is not an asserted theorem.

`Langlands.Analytic.AtlasTopology.QuasinetTopologyStatement` quantifies
over arbitrary topological spaces in two independent universes. It uses
the actual induced subspace topologies and the quasinet, net and compact
family definitions from `AtlasTopology.Definitions`.

For a quasinet, the target states that its members cover the space,
enlargement preserves the quasinet, and the whole-space singleton is a
net. Its members determine the topology: relative openness and relative
closedness test global openness and closedness, and a function to any
topological space is continuous exactly when it is continuous on every
member. The family of products of members of two quasinets is a quasinet.

If each member is compact and Hausdorff with its induced topology, the
ambient space is Hausdorff exactly when every pairwise intersection is
compact. Compactness of the members alone supplies compact
neighborhoods; when the ambient space is Hausdorff it is locally compact.
For a net of compact Hausdorff members, every pairwise intersection is
locally compact and locally closed in each of its two members.
No global Hausdorffness is assumed for that last conclusion.

The source is Vladimir G. Berkovich, *Etale cohomology for
non-Archimedean analytic spaces*, Publications mathematiques de l'IHES
78 (1993), section 1.1, printed pages 13-14 (PDF pages 10-11).
Registered source: `berkovich-1993-etale-cohomology`.
Content SHA256:
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The exact original assertions are Lemma 1.1.1(i)-(ii), the product
quasinet argument within its proof, the following local compactness
remark, and Lemma 1.1.2(i). Closedness and continuity are equivalent
reformulations of the topology assertion. Coverage, enlargement and
the singleton example follow directly from the definitions. The weak
local compactness statement records the compact-neighborhood part of
the same finite-union proof without separation assumptions.

This target does not include the separate finite-refinement assertion
of Lemma 1.1.2(ii). It does not assert the existence of affinoid domains,
a structure sheaf, an analytic atlas or an etale site. Those require
the subsequent concrete analytic constructions.
