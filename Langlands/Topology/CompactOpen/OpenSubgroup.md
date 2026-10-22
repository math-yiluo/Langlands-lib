# Proof of compact-open cofinality among open subgroups

This module proves `Langlands.OpenSubgroupContainsCompactOpen` as
`Langlands.openSubgroupContainsCompactOpen`. Worker 6 authored the Lean proof
and its original explanation in shared draft revision 3 of task
`1e120209-59a4-43b0-af06-42ff9512a8b0`. Worker 22 retained that Lean proof
unchanged, verified the exact published dependencies, and updated this
documentation for bound proof task `b500947f-5705-455b-89f6-223ac15347c3`,
revision 1. Both are actual coauthors of this submission.

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
`H.one_mem`. It applies the accepted theorem
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

## Exact accepted dependencies

All versions below were fetched as accepted and public. Both statement pairs
and the neighborhood proof pair are published and current at Library commit
`971a013122741be1a12ec337152d5dae91fb7f0b`, with no missing or changed files
and no unavailable dependencies. Their local Lean and Markdown bytes match
the published hashes.

1. The target statement is artifact
   `898ee964-4629-4f0a-9d15-9148c7e2aa21`, version 1, declaring
   `Langlands.OpenSubgroupContainsCompactOpen` in
   `Langlands.Topology.CompactOpen.OpenSubgroupStatement`.
   Its target fingerprint is
   `c8483cdacdf9b5daa37466dd1ea90b8a35244921a1e313233ce4c9cde9c1c97b`.
   Reviewer 22 independently approved it, with final publication receipt
   `dd30ce73-3f01-4077-9bf1-56e4dbe14476` and domain evidence
   `5c465626-2aea-4899-9def-c7a5fe73f5ef`.
   It was published at commit `40c7486eb2f63407d8cb3616d80706fde8bd441b`,
   snapshot `7442cf96123133ffcba08c82afd749dfbbfbfd1ac5f44e9f124b30b9bf16d190`.
   Its Lean SHA-256 is
   `60afba3f56e64cc11f643a37243af96c87c9a4543512e2f608927852ee7e0d34`;
   its Markdown SHA-256 is
   `0e24f945bef999534689d2d74b6e9a5a678320e4de15267a957a85be08bdca00`.
2. The applied proof is artifact `d611373d-18d1-42d9-8201-09b30461afd3`,
   version 1, declaring `Langlands.compactOpenSubgroupBasis` in
   `Langlands.Topology.CompactOpen.NeighborhoodBasis`, produced by task
   `83c9e2e3-7d24-4ae8-ba36-8fda72b4f789`, revision 1.
   Worker 6 authored that proof; Worker 10 verified its dependencies and
   prepared its submission. Registered independent checker evidence
   `0dd9950d-38bd-40d2-920e-0f7d8469a987` accepts the proof.
   Reviewer 30 independently approved and published it with final receipt
   `ffcccc39-9099-4c3b-abc1-f5be3bf46ebd`, integration
   `ed969d4e134c4a0f8c38478cd8fec1c9`, commit
   `971a013122741be1a12ec337152d5dae91fb7f0b`, and snapshot
   `f7eb930eed7192808b61115d2d9668f0ed13bab7255ca9f3b3945af3e2f48af2`.
   Its Lean SHA-256 is
   `5b5322b631663241c1295826da02d7a43cc585566124c5a426020c19c642a6b9`;
   its Markdown SHA-256 is
   `0b258f936bb5e0d99be3608077bcdc7da3a2b885aaed75b2c273a633fe2cea7e`.
3. The proof's statement dependency is artifact
   `25905329-f69e-4866-b0e7-97673395dd3b`, version 1, declaring
   `Langlands.CompactOpenSubgroupBasis` in
   `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement`.
   Its target fingerprint is
   `2b600b47776f14540a51a96d886dc9d49a0971a06eb93d30245f654c73bca237`.
   Reviewer 19's final receipt is `f8d4bd58-cddf-4209-8a05-e4c04e1061af`,
   and its domain evidence is `43e162a8-fd44-423a-b020-9d181154283c`.
   Its publication commit is `06637e1639c8f200329f6ae563cc4ca422a61c11`.
   Its Lean SHA-256 is
   `80d23d1a0faa606af6610f3a306b130c28739e12d51f533c52862fd45a220131`;
   its Markdown SHA-256 is
   `f5a2a0045ab6a79fc96e5681a78be891c9f16fcd9514126b87f4625aeb761532`.
4. The accepted prepared environment is artifact
   `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
   Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
   and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
   Its operator acceptance receipt is
   `c63dc28a-ea77-4b5d-a0f0-e926e261d634`.

The two direct project imports are the neighborhood proof module and the
target statement module. The neighborhood statement is a transitive import.
There are no additional project definition dependencies.

## Provenance and validation boundary

This is an internal corollary of the accepted compact-open neighborhood
theorem. Worker 22 checked `OpenSubgroup.mem_nhds_one` and the `SetLike`
partial-order instance in the pinned
`Mathlib/Topology/Algebra/OpenSubgroup.lean`, lines 118-119 and 79.
The Lean source has SHA-256
`7525db5999eead45f1937386afca5bb1922612966bf0d2c55bdb8949cf66ef70`,
matching Worker 6's original draft.

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter I, revision April 18, 2024, Section 6, printed/PDF page 8, opening
LP group definition, motivates the terminology. That definition assumes a
Hausdorff topology and a compact-open subgroup neighborhood basis; it does
not prove this corollary from Mathlib's hypotheses. Worker 22 read the
retained original passage and verified its source hash.
Literature ID: `casselman-2024-profinite-analysis`; source SHA-256:
`16c37c57578aa1463c5625744cdade16416c5afb16b9e2203f13de4355a70270`.
Actual retained original:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter I - Analysis on profinite groups--2024.pdf`.

Local compilation is development evidence only. Acceptance of this corollary
requires its own registered independent checker and independent semantic
review and publication; the accepted dependencies alone do not supply them.
