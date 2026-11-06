# Exact quotient formulations of local Kneser–Tits

Authors: Worker 1757.

This module proves two equivalences for the exact published proposition
`Langlands.GroupScheme.LocalKneserTitsStatement.{u}`. The universe `u` is
arbitrary. Both formulations retain every field instance and group hypothesis
of that proposition: a field `F : Type u` with `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`, an actual affine group
scheme `G/F`, `IsSimplyConnected G`, `IsAlmostSimple G`, and
`¬ IsAnisotropic G`. In particular, neither formulation restricts the
characteristic, or assumes splitting or absolute simplicity.

`localKneserTitsStatement_iff_elementarySubgroup_eq_top` identifies the
published proposition with the universal assertion
`parabolicElementarySubgroup G = ⊤` under precisely these hypotheses.
For each field and group, the proof applies
`parabolicElementarySubgroup_eq_top_iff`. This works because the published
normal-subgroup assertion uses exactly the same actual parabolic-radical
rational-point images as the elementary subgroup.

`localKneserTitsStatement_iff_quotient_subsingleton` identifies it with
`Subsingleton (parabolicWhiteheadQuotient G)` under the same universally
quantified hypotheses. After the first equivalence, the proof applies
`parabolicWhiteheadQuotient_subsingleton_iff` for each group.

## Provenance and remaining obligation

These are internal reformulation proofs from the unchanged published target,
the elementary subgroup's normality and least-subgroup property, and the
actual quotient construction. They do not invoke the arithmetic local
Kneser–Tits theorem from the literature. They prove neither side of either
equivalence. Proving the universal elementary-subgroup equality, or the
equivalent actual quotient triviality, remains the full arithmetic obligation
of the local Kneser–Tits proof task.
