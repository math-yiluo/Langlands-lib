# Evaluation and total disconnectedness of canonical rational points

Author: Worker 200.

This derived adapter constructs a continuous evaluation map from the existing
identity-test rational points of an affine scheme to the product of copies of
its base ring indexed by global coordinates. Its source topology is exactly
`rationalPointTopology`; no global rational-point topology instance is added.
The map is the published identity-test comparison, followed by the affine
global-section point comparison and `AlgPoint.evaluation`. The application
identity is definitional, and the embedding theorem composes the two published
homeomorphisms with the published evaluation embedding.

Products of totally disconnected spaces are totally disconnected, as are
subspaces. This proves the corresponding property for algebra-map points
with independent base, coordinate and value universes, and for the canonical
points of any affine scheme over a totally disconnected ring. These results
require no finite type, group structure, Hausdorffness or continuity of ring
operations.

The helper `valuativeNonarchimedeanRing` transports Mathlib's nonarchimedean ring
certificate along `Valuation.toTopologicalSpace_eq`, for the supplied valuative
topology. The field specialization reuses the published theorem
`Langlands.BruhatTits.localField_totallyDisconnectedSpace` from
[RationalPointCompactOpen](../../BruhatTits/Unipotent/RationalPointCompactOpen.md)
through `nonarchimedeanLocalFieldTotallyDisconnected`. That theorem introduces
a compatible additive uniformity locally, obtains Hausdorffness from the
valued-field instances, and applies Mathlib's nonarchimedean additive-group
result. Applying the evaluation embedding proves
`rationalPoint_totallyDisconnectedSpace_of_localField` for every affine scheme
over any `IsNonarchimedeanLocalField`, in arbitrary universe and characteristic.

Provenance: this is an internal deduction from the published affine evaluation
and rational-point comparisons and pinned Mathlib's valuative-topology,
nonarchimedean-group and product/subspace topology results. It supplies the
total-disconnectedness portion of the topology described in Renard V.1–V.2.1,
printed pp.103–104 / PDF pp.109–110
(`renard-2026-representations-groupes-reductifs-padiques`, 9 July 2026 edition).
Renard obtains the group topology from an embedding into a general linear
group; the present proof instead uses all global coordinates of the affine
scheme. Waldspurger I.1, printed pp.238–239 / PDF pp.4–5
(`waldspurger-2003-plancherel`), fixes the rational-point group setting for
which this is a prerequisite; that passage is motivation, not the source
of the evaluation-embedding argument. This module does not reconstruct
the algebraic structural inputs of either source.

This module does not establish rational-point topological-group laws, local
compactness, second countability, compact open subgroup bases, closed-immersion
comparisons or any character-lattice or Plancherel conclusion. Those results
require their separate hypotheses and comparisons. In particular, total
disconnectedness alone does not supply a nonarchimedean multiplicative group
structure.
