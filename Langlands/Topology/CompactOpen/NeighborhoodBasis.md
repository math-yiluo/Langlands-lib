# Proof of the compact-open neighborhood basis

This module proves `Langlands.CompactOpenSubgroupBasis`, the statement of
`Langlands.Topology.CompactOpen.NeighborhoodBasisStatement`.

## Implemented proof and hypotheses

The theorem `Langlands.compactOpenSubgroupBasis` proves that every identity
neighborhood U in a group G with a topology, `NonarchimedeanGroup G`, and
`WeaklyLocallyCompactSpace G` contains a compact open subgroup. It is universal
in the universe of G. No separation assumption is present.

1. `exists_compact_mem_nhds (1 : G)` gives a set C, a proof of its compactness,
   and membership of C in the identity-neighborhood filter.
2. `Filter.inter_mem hU hC` proves that U intersect C is a neighborhood.
3. `NonarchimedeanGroup.is_nonarchimedean` gives `K : OpenSubgroup G` contained
   in that intersection.
4. `K.isClosed` proves its underlying set is closed. This uses Mathlib's
   `SeparatelyContinuousMul` instance, inherited from the topological-group
   instance supplied by `NonarchimedeanGroup`.
5. For each x in K, the second projection of the intersection inclusion places
   x in C. `hCc.of_isClosed_subset` therefore proves K compact.
6. The first projection of the same inclusion places every x of K in U.

Closed subsets of compact sets are compact without Hausdorff assumptions.
This explains the strengthening of the locally compact Hausdorff
case. Mathlib supplies `WeaklyLocallyCompactSpace` from `LocallyCompactSpace`.
The proof uses no compact-open basis axiom or substitute group structure.

## Provenance and dependencies

This is an internal proof using the Mathlib interfaces audited in the paired
statement Markdown. The motivating source is Casselman, *Introduction to
admissible representations of p-adic groups*, Chapter I, revision April 18,
2024, Section 6, printed/PDF page 8, opening LP group definition. That source
assumes the compact-open basis; the present implication is proved from
Mathlib's separate hypotheses, not quoted as a theorem from that source.
Literature ID: `casselman-2024-profinite-analysis`; SHA-256:
`16c37c57578aa1463c5625744cdade16416c5afb16b9e2203f13de4355a70270`.
Actual retained original:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter I - Analysis on profinite groups--2024.pdf`.

The sole project import is the exact neighborhood statement named above.
The environment is Lean
4.34.0 at commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
