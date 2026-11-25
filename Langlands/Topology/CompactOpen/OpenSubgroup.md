# Proof of compact-open cofinality among open subgroups

This module proves `Langlands.OpenSubgroupContainsCompactOpen` as
`Langlands.openSubgroupContainsCompactOpen`.

## Implemented proof and hypotheses

The theorem directly inhabits `OpenSubgroupContainsCompactOpen.{u}`. It
quantifies over every type `G : Type u`, its `Group G` and `TopologicalSpace G`
instances, `NonarchimedeanGroup G`, `WeaklyLocallyCompactSpace G`, and every
`H : OpenSubgroup G`. Its conclusion is the existence of `K : OpenSubgroup G`
with `IsCompact (K : Set G)` and `K <= H`. Compactness and openness refer to
the ambient group.

After introducing these variables, the proof uses `H.mem_nhds_one` to show
that the underlying set of H belongs to the neighborhood filter of the
identity. In the pinned Mathlib source this follows from `H.isOpen` and
`H.one_mem`. It applies the Library theorem
`Langlands.compactOpenSubgroupBasis` to G, the set `(H : Set G)`, and this
neighborhood proof. The resulting open subgroup K has compact underlying
set and is contained in H. Mathlib's order on open subgroups is definitionally
underlying-set inclusion, so the result directly has the required conclusion
`K <= H`; no additional conversion lemma is needed.

The compact-open neighborhood basis is used as a proved theorem under these
same hypotheses, never as an additional assumption. No separation hypothesis
or representation structure is required. In particular, Mathlib supplies
`WeaklyLocallyCompactSpace G` from `LocallyCompactSpace G`, so the theorem
includes the locally compact Hausdorff specialization.

## Exact dependencies

1. The target statement is
   `Langlands.OpenSubgroupContainsCompactOpen` in
   `Langlands.Topology.CompactOpen.OpenSubgroupStatement`.
2. The applied proof is `Langlands.compactOpenSubgroupBasis` in
   `Langlands.Topology.CompactOpen.NeighborhoodBasis`.
3. The proof's statement dependency is
   `Langlands.CompactOpenSubgroupBasis` in
   `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement`.
4. The environment is
   Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
   and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The two direct project imports are the neighborhood proof module and the
target statement module. The neighborhood statement is a transitive import.
There are no additional project definition dependencies.

## Provenance

This is an internal corollary of the compact-open neighborhood
theorem. `OpenSubgroup.mem_nhds_one` and the `SetLike`
partial-order instance were checked in the pinned
`Mathlib/Topology/Algebra/OpenSubgroup.lean`, lines 118-119 and 79.

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter I, revision April 18, 2024, Section 6, printed/PDF page 8, opening
LP group definition, motivates the terminology. That definition assumes a
Hausdorff topology and a compact-open subgroup neighborhood basis; it does
not prove this corollary from Mathlib's hypotheses. The
retained original passage was read and its source hash verified.
Literature ID: `casselman-2024-profinite-analysis`; source SHA-256:
`16c37c57578aa1463c5625744cdade16416c5afb16b9e2203f13de4355a70270`.
Actual retained original:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter I - Analysis on profinite groups--2024.pdf`.
