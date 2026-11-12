# Renard II.3.3: an orbit quotient need not be Hausdorff

This statement formalizes the warning in David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, II.3.3,
printed p.44 / PDF p.50, in the paragraph immediately before the Lemma.
Source ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`Langlands.Topology.RenardOrbitQuotient.NonHausdorffOrbitQuotientStatement`
asserts that there exist small types `G` and `X`, a group structure on `G`,
topologies on both, and a group action on `X`, such that `G` is a topological
group, the action is continuous, both spaces are locally profinite, and the
actual orbit quotient `Quotient (MulAction.orbitRel G X)` fails to be Hausdorff.
The quotient carries Mathlib's quotient topology. The existential structures
are installed as local instances, so the continuity and separation predicates
refer to those same structures and action. The source's t.d. hypotheses are
expressed by the existing `Langlands.Topology.IsLocallyProfinite` predicate;
its equivalence with Hausdorff locally compact totally disconnected spaces is
proved in `Langlands/Topology/LocallyProfinite.lean`.

This is an existential counterexample statement. It neither assumes a
non-Hausdorff space as an input nor weakens the separation hypotheses on `G`
or `X`. A potential proof route is the discrete integer group acting by
translations on its one-point compactification and fixing the point at
infinity. The statement does not prescribe that construction, and no proof
or witness is supplied here. The existing six-target topology statement
bundle remains unchanged.
