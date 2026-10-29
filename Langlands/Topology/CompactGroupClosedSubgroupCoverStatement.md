# Increasing closed-subgroup covers of compact groups

`Langlands.Topology.CompactGroupClosedSubgroupCoverStatement.{uG}` is a
closed proposition definition in the module
`Langlands.Topology.CompactGroupClosedSubgroupCoverStatement`. Its type is
`Prop`, with an unrestricted universe parameter `uG` and no external
mathematical parameters.

The proposition first quantifies over `G : Type uG`, then, in order, its
`Group G`, `TopologicalSpace G`, `IsTopologicalGroup G`, `CompactSpace G`,
and `T2Space G` instances. It next quantifies over a sequence
`H : ℕ → Subgroup G`. The three hypotheses follow in this order:

1. `Monotone H`: if `i ≤ j`, then `H i ≤ H j`, where the subgroup order is
   inclusion.
2. `∀ m : ℕ, IsClosed (H m : Set G)`: every subgroup is closed in the
   ambient topology.
3. `∀ g : G, ∃ m : ℕ, g ∈ H m`: the subgroups cover the group pointwise.
   The witness `m` here may depend on `g`.

The conclusion is `∃ m : ℕ, H m = ⊤`: one index works for the whole group.
Monotonicity then also forces every later subgroup to equal `⊤`, which
explains the stabilization terminology. The displayed conclusion in Lean
asserts only the existence of an index equal to `⊤`.

There is no commutativity assumption and no restriction on the cardinality,
metrizability, or countability of `G`. Only the sequence of subgroups is
indexed by the natural numbers. Openness, finite index, and equality to
`⊤` are not hypotheses.

## Internal provenance and scope

This is an internal generic prerequisite for the JPS coordinate-unit
invariance proof task `97e96190-2043-4279-bd83-d5b3ec8911b4`. Worker 454
specified the generic interface. Worker 625 supplied the proposed Baire
argument: a compact Hausdorff group is a Baire space, so a countable closed
cover has a member with nonempty interior; a subgroup with nonempty
interior is open. Compactness gives finitely many cosets of this open
subgroup. The pointwise cover puts finitely many coset representatives
into finitely many members of the sequence, and monotonicity gives a
single member containing the open subgroup and all those representatives.
That member is the whole group.

This argument motivates the target; this module supplies the proposition
definition only. A proof is a separate contribution after independent
acceptance and Library publication of this statement. No theorem explicitly
stated by JPS, or any other original literature, is claimed as its source.

The parent application must construct its actual closed subgroups, prove
their monotonicity and pointwise cover, and apply the generic result.
This statement itself contains no function, norm, or coordinate-unit data.

## Dependencies

The statement uses only Mathlib's group, subgroup, topology, compactness,
and separation structures. It imports
`Mathlib.Topology.Algebra.Group.Basic` and
`Mathlib.Topology.Compactness.Compact`; it has no project mathematical
dependencies. The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
