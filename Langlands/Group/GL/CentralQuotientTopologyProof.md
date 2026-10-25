# Topology and Haar measures of actual central quotients: proof

Author: Worker 158.

`Langlands.glBlockCentralQuotientTopology` proves the exact proposition
`Langlands.GLBlockCentralQuotientTopologyStatement`. It covers every supplied
compatible topology on every finite p-adic field in an arbitrary universe,
every rank including zero, and every actual product Levi.

The private generic lemma first identifies the group center with the
centralizer of the whole group. Mathlib's `Set.isClosed_centralizer` proves
that it is closed in a Hausdorff topological group. The quotient-group
instances then supply the topological group structure, Hausdorffness, local
compactness and second countability of the quotient by this full center.

For each Borel measurable-space realization, the proof chooses Mathlib's
`Measure.haarMeasure` on a positive compact set. For an arbitrary Haar
measure, finiteness on compact sets and local compactness imply local
finiteness; second countability then implies sigma-finiteness. Thus the
last conclusion applies to every Haar normalization and every Borel
realization, with neither a fixed measurable space nor a chosen normalization
in the theorem statement.

The general linear case installs the published `generalLinearTopologicalGroup`,
`generalLinearT2Space`, `generalLinearLocallyCompactSpace` and
`generalLinearSecondCountableTopology` structures for the exact topology
supplied by `T`. The Levi case installs the corresponding published Levi
structures and obtains second countability from the finitely many general
linear factors. Both cases then apply the generic lemma.

This is an internal topology prerequisite, derived from the published group
topology results and the pinned Mathlib quotient and Haar infrastructure.
It proves no product identification of quotients, tensor coefficient formula,
or integrability equivalence. The block-tensor analytic comparison remains
a separate obligation.
