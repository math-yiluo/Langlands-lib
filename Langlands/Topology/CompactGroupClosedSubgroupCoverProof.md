# Stabilization of an increasing closed-subgroup cover

`Langlands.Topology.compactGroupClosedSubgroupCover.{uG}` proves the entire
unapplied Library proposition
`Langlands.Topology.CompactGroupClosedSubgroupCoverStatement.{uG}`. The
proof imports that statement by its Lean module name and introduces no
external mathematical parameters or additional hypotheses. It applies to
arbitrary compact Hausdorff topological groups, without commutativity or
any countability condition on the group.

## Implemented proof

The pointwise cover is first expressed as the equality of the countable
union of the closed subgroups with the whole group. Compact Hausdorff
spaces are locally compact and Baire, so
`nonempty_interior_of_iUnion_of_closed` supplies an index `m` and a point
in the interior of `H m`. A subgroup that is a neighborhood of any point
is open, by `Subgroup.isOpen_of_mem_nhds`.

For each natural number `n`, consider `H (max m n)`. Monotonicity and
`Subgroup.isOpen_mono` show that all these subgroups are open. They still
cover the group: an element in `H n` belongs to `H (max m n)`. They form
a directed cover because the member indexed by `max i j` contains the
members indexed by `i` and `j`. Compactness, in the form
`IsCompact.elim_directed_cover` applied to the whole group, supplies one
member containing the whole group. That subgroup equals `⊤`, as required.

The countability needed for Baire concerns only the sequence indexed by
`ℕ`. Openness is deduced inside the proof. No finite-index, normality,
commutativity, or metrizability assumption is used.

## Internal provenance and scope

The generic interface was specified for the JPS coordinate-unit
invariance application. The proof follows the Baire argument leading
to an open subgroup and completes that argument by the directed
open-cover form of compactness. This final step
absorbs the finite-subcover and maximum-index argument directly, without
choosing coset representatives.

This is an internal generic lemma, not a theorem explicitly stated by
JPS or other original literature. The JPS application
(`Langlands.Whittaker.jpsCoordinateUnitInvariance`, module
`Langlands.Representation.Whittaker.JPSCoordinateUnitInvarianceProof`)
constructs its actual closed subgroups, proves their monotonicity and
pointwise cover, and applies this theorem to obtain coordinate-unit
invariance.

## Dependencies

The proof uses the published statement and Mathlib's open-subgroup,
Baire, and locally compact Baire-space APIs. The environment is
Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
