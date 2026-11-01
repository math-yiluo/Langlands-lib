# Renard II.1.1: proofs for locally profinite spaces and groups

This proof-only unit proves the exact public target
`Langlands.Topology.LocallyProfiniteStatements.LocallyProfiniteAssertions`.
The statement is imported unchanged by Lean name from
`Langlands.Topology.LocallyProfiniteStatements`; no copied statement files
are included. The four component theorems and the aggregate preserve the
independent space/group universe uX and family universe uI.

Worker 6 authored the Lean proof. Worker 1218 checked the public imports,
source correspondence and proof documentation. Development check
`fc155c13-8374-4025-8ef4-c28e936a625f` compiled this proof against the published
statement with zero errors or warnings. Declaration inspection reported the
independent universes uX/uI and only propext, Classical.choice and Quot.sound.
This development check is separate from exact-target validation and independent
semantic review.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.1.1, printed page 30 /
PDF page 36, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Workers 6 and 1218 read this entire page, including both lemma proofs and the Baire
reference. The source names Van Dantzig for the subgroup characterization
and [26], Theorem XI.10.1, for Baire. The registered 2010 supplement's
PDF page 2 Baire correction was also checked; the governing 2026 wording
already asserts density of the intersection of dense opens.

## Implemented arguments

The private helper `compactOpenMulNhd` applies compact-set induction to the
given compact open set `W`. The induction assertion for a compact portion
`S` asks for one identity neighborhood `T` with `S * T ⊆ W`. It is stable
under subsets and finite unions, intersecting the two neighborhoods in the
union step. At each point, continuity of multiplication gives product
neighborhoods contained in `W`.

`openSubgroupInCompactOpen` shrinks `T` to an open identity neighborhood
`U` and replaces it by the symmetric `V = U ∩ U⁻¹`. Right multiplication
by `V` preserves `W`. The union of its positive powers is a subgroup:
multiplication adds the exponents, symmetry gives inverse closure, and
the identity belongs to `V`. Each positive power is open. Induction shows
`W * V^(n+1) ⊆ W`; since `1 ∈ W`, every power lies in `W`.

This argument adapts the three Mathlib proofs
`IsTopologicalGroup.exist_mul_closure_nhds`,
`IsTopologicalGroup.exists_mulInvClosureNhd` and
`IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one` in
`Mathlib/Topology/Algebra/OpenSubgroup.lean`, whose authors and Apache 2.0
notice are retained in the Lean file. The adaptation uses explicit compactness
of `W` in the first induction and needs no global compactness of the group.

For the forward direction of `vanDantzig`, the source predicate supplies a
compact open identity neighborhood `W` inside any requested neighborhood.
The subgroup just constructed is closed, as every open subgroup is, and
therefore compact as a closed subset of `W`. For the reverse direction,
translate the supplied compact-open subgroups by left multiplication to get
compact-open neighborhoods at arbitrary points. Continuity and openness of
left translation use the original group and topology. Hausdorffness is
retained as the explicit conjunct of the target. No nonarchimedean assumption
is added.

`locallyClosedSubspaces` installs the Hausdorff, locally compact and totally
disconnected structures extracted from the public source predicate. Mathlib's
`IsLocallyClosed.locallyCompactSpace` gives local compactness of the actual
subtype; the other two properties are inherited by subspaces. The published
reverse correspondence gives the source predicate for that subtype.

For `finiteDisjointRefinement`, first choose for each point of `K` an original
cover member containing it, then a compact open neighborhood within that
member. Compactness of `K` gives a finite subcover, which is enumerated by
`Fin n`, including `n = 0` when empty. Apply Mathlib's `disjointed` operation
to subtract the earlier members from each enumerated set.
`disjointedRec` proves these sets remain clopen, `disjoint_disjointed` gives
pairwise disjointness, and `iSup_disjointed` preserves the union. Each new
set lies inside its original compact set, so its closedness gives compactness
and the original subordinate inclusion persists. This implements the source's
finite disjointification argument in the ambient space.

For `denseOpenIntersections`, extract Hausdorffness and local compactness.
The existing Mathlib locally compact R1 Baire instance applies, and
`dense_iInter_of_isOpen` gives exactly the target for an arbitrary countable
index type. No size or countability condition on the ambient space is used.

The final theorem packages these four targets without changing their
statements. Space/group and cover/intersection universes remain independent.
All sets, subgroups, subtype topologies and translations are actual objects
in the specified ambient structures.

## Mathlib proof sources

The alternate routes above use Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, in the approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The following registered source files
make the implementation provenance explicit.

| Registered source | File under `Mathlib/` and locator |
| --- | --- |
| `mathlib-open-subgroup-5ed296525643` | `Topology/Algebra/OpenSubgroup.lean`, the three compact-clopen-neighborhood arguments named above, lines 575–644 |
| `mathlib-locally-compact-5ed296525643` | `Topology/Compactness/LocallyCompact.lean`, `IsLocallyClosed.locallyCompactSpace` and its inducing-map proof, lines 196–218 |
| `mathlib-disjointed-5ed296525643` | `Order/Disjointed.lean`, `disjointed`, `disjointedRec`, `disjoint_disjointed` and `iSup_disjointed`, lines 59, 97, 206 and 302 |
| `mathlib-baire-locally-compact-5ed296525643` | `Topology/Baire/LocallyCompactRegular.lean`, `BaireSpace.of_t2Space_locallyCompactSpace`, lines 23–59 |
| `mathlib-baire-lemmas-5ed296525643` | `Topology/Baire/Lemmas.lean`, `dense_iInter_of_isOpen`, lines 138–144 |
