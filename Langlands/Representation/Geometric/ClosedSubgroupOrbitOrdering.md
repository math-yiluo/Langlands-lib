# Finite closed-subgroup double-coset orbit ordering

The theorem `Langlands.Geometric.closedSubgroupOrbitOrdering` proves exactly
`Langlands.Geometric.ClosedSubgroupOrbitOrdering.{uG}` from
`Langlands.Representation.Geometric.ClosedSubgroupStatement`. The theorem is
unapplied and retains the arbitrary group universe. The statement module, its
Markdown, and its imports are unchanged.

For every Hausdorff, locally compact, sigma-compact nonarchimedean group `G` and
closed subgroups `P` and `Q`, finiteness of the actual Mathlib double-coset
quotient yields `n : ℕ` and an `OrderedDoubleCosets P Q n`. Its representatives
give a pairwise disjoint cover of `Induction.LeftQuotient P` by actual
`cosetOrbit` sets, and every initial union is open. The representative convention
is exactly `P w⁻¹ Q`.

## Implemented proof

The closing proof applies the published
`closedSubgroupOrbitOrdering_of_finiteOrbitOrdering` to the published theorem
`Langlands.Topology.finiteOrbitOrdering.{uG, uG}`. Both the acting subgroup `Q`
and the quotient space have universe `uG`, so this is an unapplied proof of the
original target with no additional premise.

The imported specialization performs the following construction. Closedness of
`Q` supplies sigma compactness of `Q`; the quotient topology results give local
compactness of `P \ G` and, using closedness of `P`, Hausdorffness. The action
`q • P g = P g q⁻¹` is jointly continuous. The equivalence
`doubleCosetEquivOrbitQuotient` identifies the actual double-coset quotient with
the action orbit quotient, so the latter is finite.

The generic theorem provides quotient points `r i` with a disjoint orbit cover
and open initial unions. Choose group elements `g i` lifting these points, and
set `w i = (g i)⁻¹`. The equality
`MulAction.orbit Q (r i) = cosetOrbit P Q (w i)` transfers coverage,
disjointness and openness to the three fields of `OrderedDoubleCosets`.

The imported generic proof establishes the ordering by Baire category and
induction on the number of orbit classes meeting a closed invariant set.
Compact pieces of the sigma-compact acting group give a countable closed cover
by subsets of orbits. Baire category yields one piece with nonempty relative
interior; translating it gives a relatively open orbit. Removing that orbit
leaves a closed invariant set with fewer orbit classes. The induction prepends
the removed orbit and proves openness of each initial union. Its relative
formulation adjoins the complement of the closed invariant set to those unions.
Applying it to the whole quotient space gives the required ordering.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`. Neither an
ordering nor orbit local closedness is an additional assumption.

## Provenance and scope

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), section 5.1, printed pages 459–460, describes the inverse right action
on `P \ G` and numbers its finitely many orbits with open initial unions. It
cites Bernstein–Zelevinsky, *Representations of the group GL(n,F) where F is a
non-archimedean local field* (1976), section 1.5, printed page 7. These retained
original passages were read during this task; the registered literature IDs
are `bernstein-zelevinsky-1977-induced-i` and
`bernstein-zelevinsky-1976-representations-gln`.

The generic topological proof is the published internal generalization explained
in `Langlands/Topology/GroupAction/FiniteOrbitProof.md`. It proves the ordering
using the argument above without needing the stronger orbit-map openness
assertion or a compact-open subgroup basis. This module specializes that result
to the published closed-subgroup target. The natural Mackey graded-piece theorem
and the full geometric lemma remain separate results.
