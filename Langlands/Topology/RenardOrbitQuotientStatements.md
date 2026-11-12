# Renard II.3.3–II.3.4: orbit maps and quotients

This unit states six results in
`Langlands.Topology.RenardOrbitQuotient.Statements`. They are proposition
definitions, with no proofs supplied here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The exact locations are II.3.3 Proposition, Lemma and following paragraph,
printed p.44 / PDF p.50; II.3.3 Corollary and II.3.4 Lemma, printed p.45 /
PDF p.51.

All spaces use their supplied topologies. Renard's t.d. condition is the
published `Langlands.Topology.IsLocallyProfinite`, including Hausdorffness and
a compact open neighborhood basis. Its equivalence with the Hausdorff, locally
compact, totally disconnected Mathlib conditions is already proved in
`isLocallyProfinite_iff_mathlib`. Actions are actual `MulAction`s with
`ContinuousSMul`; no action continuity or separation is implicit in prose.
The universes of the group and acted-on space are independent.

The six targets are:

1. `FiniteOrbitOpenOrbitStatement`: a sigma-compact t.d. group acting with
   finitely many orbits on a **nonempty** t.d. space has an open orbit, and
   the orbit map at every point of that orbit is open. The Lean map has
   codomain the ambient space; since the orbit is open, this is equivalent
   to openness as a map onto the orbit with its subspace topology.
2. `FiniteOrbitsLocallyClosedStatement`: under the same conditions, with
   nonemptiness unnecessary, every orbit is locally closed.
3. `InvariantQuotientImagesStatement`: invariant closed and locally closed
   subsets have closed and locally closed images in the actual
   `Quotient (MulAction.orbitRel G X)`.
4. `HausdorffOrbitQuotientStatement`: if that quotient is Hausdorff, it is
   locally profinite.
5. `TransitiveQuotientHomeomorphismStatement`: for a transitive action, a
   homeomorphism from the actual subgroup quotient by the point stabilizer
   exists and satisfies `e (gH) = g • x`. Thus the canonical orbit map,
   rather than an unspecified homeomorphism type, is identified.
6. `ClosedSubgroupQuotientStatement`: quotient by any closed subgroup is
   locally profinite. When the subgroup is normal, Mathlib's existing
   `QuotientGroup.instIsTopologicalGroup` supplies the topological group
   structure on the same quotient, completing the second sentence of
   II.3.4.

The nonempty hypothesis in target 1 is a correction to the literal printed
Proposition: the empty space has finitely many orbits but has no orbit at all.
The source's proof chooses orbit representatives and tacitly assumes one
exists. No nonemptiness restriction is added to the locally closed assertion.
The Corollary already supplies a point and hence does not need a separate
nonempty hypothesis.

Mathlib already proves that the orbit projection is open:
`MulAction.isOpenQuotientMap_quotientMk`, in
`Mathlib.Topology.Algebra.ConstMulAction`, applies to the same quotient and
projection, using the `ContinuousConstSMul` instance induced by
`ContinuousSMul`. It also proves continuity of the quotient projection and
`QuotientGroup.instLocallyCompactSpace` for subgroup quotients. These results
are reused; no replacement quotient carrier is introduced. They do not by
themselves establish the six new targets, which remain unproved.
