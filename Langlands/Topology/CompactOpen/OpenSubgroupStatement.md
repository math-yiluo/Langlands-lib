# Compact open subgroups inside open subgroups

`Langlands.OpenSubgroupContainsCompactOpen` is a proposition definition. For
every group `G` in an arbitrary universe, equipped with a topology,
`NonarchimedeanGroup G`, and `WeaklyLocallyCompactSpace G`, and every
`H : OpenSubgroup G`, it asserts the existence of `K : OpenSubgroup G` with
`IsCompact (K : Set G)` and `K <= H`. Mathlib's order on `OpenSubgroup G`
is inclusion of the underlying sets, so this says that the compact open
subgroup lies inside `H`. Compactness and openness are in the ambient group.

This is the cofinality statement needed to pass from tests over all open
subgroups to tests over the compact open subgroups. No representation-theoretic
conclusion is asserted here.

## Hypotheses and provenance

This is an internal corollary target. Every open subgroup contains the identity
and is therefore a neighborhood of it (`OpenSubgroup.mem_nhds_one`). Applying
the compact-open neighborhood result to that neighborhood gives precisely the
asserted inclusion. The proof will be submitted separately after the target
is independently accepted and published.

Mathlib's `NonarchimedeanGroup` supplies continuity of the group operations
and the open-subgroup neighborhood property. Weak local compactness supplies
a compact neighborhood at each point. No separation assumption is made.
The stronger Mathlib hypothesis `LocallyCompactSpace G` supplies
`WeaklyLocallyCompactSpace G`, so this covers the originally requested
locally compact Hausdorff case.

The terminology is motivated by Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter I: *Analysis on profinite groups*,
revision April 18, 2024, Section 6, printed/PDF page 8, opening definition of an
LP group. That definition assumes a Hausdorff topology and a compact-open
subgroup neighborhood basis; it is not a proof of this bridge from Mathlib's
hypotheses. This target is internally derived and does not assert a theorem
about all totally disconnected locally compact groups.

- Literature ID: `casselman-2024-profinite-analysis`.
- Source SHA-256:
  `16c37c57578aa1463c5625744cdade16416c5afb16b9e2203f13de4355a70270`.
- Actual retained original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter I - Analysis on profinite groups--2024.pdf`.

## Interface audit and exact dependencies

Worker 6 inspected `OpenSubgroup.mem_nhds_one` and the `SetLike` partial-order
instance in the pinned `Mathlib/Topology/Algebra/OpenSubgroup.lean`. Existing
`OpenSubgroup` already bundles all required algebra and openness data.
No new group structure or compact-open basis axiom is needed.

There are no project mathematical dependencies for this statement. It imports
`Mathlib.Topology.Algebra.Nonarchimedean.Basic` and
`Mathlib.Topology.Compactness.LocallyCompact`. The prepared environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`: Lean 4.34.0 at commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The Lean file defines the target only. Compilation establishes elaboration;
semantic acceptance and publication require independent review.
