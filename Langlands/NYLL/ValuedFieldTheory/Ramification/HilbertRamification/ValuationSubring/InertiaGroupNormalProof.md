# The inertia group is normal in the decomposition group (NYLL M239.005)

This module proves
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal.{u, v}`
and registers it as a global instance. Its type is exactly the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normalStatement.{u, v}`
(an `abbrev`), imported from
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Statements`.
This is source unit M239.005, a Prop-valued instance in the source.

## Statement proved

```lean
abbrev inertiaGroup_normalStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    (inertiaGroup K A).Normal
```

For every field extension `L / K` (universes `u`, `v` arbitrary, no further hypothesis) and
every valuation subring `A` of `L`, the inertia group `inertiaGroup K A` is a normal
subgroup of the decomposition group `decompositionGroup K A`.

## Implemented proof and instance registration

```lean
theorem inertiaGroup_normal : inertiaGroup_normalStatement.{u, v} := by
  intro K L _ _ _ A
  change (MonoidHom.ker (residueAction K A)).Normal
  infer_instance

attribute [instance] inertiaGroup_normal
```

After introducing the binders, `change` replaces the goal by the normality of the kernel of
the residue action. This is a definitional step: `inertiaGroup K A` is the published
abbreviation for Mathlib's `A.inertiaSubgroup K`, which Mathlib defines as the kernel of
`MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)`, and
`residueAction K A` is the published abbreviation for that map. `infer_instance` then finds
Mathlib's instance `MonoidHom.normal_ker` (`Mathlib/Algebra/Group/Subgroup/Ker.lean`): the
kernel of a monoid homomorphism from a group is normal.

`attribute [instance] inertiaGroup_normal`, in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`, registers the
theorem as a global instance, as the source's `instance` declaration does. This works
because the target is a reducible `abbrev`, so the theorem's type unfolds to a `∀` ending in
the class `Subgroup.Normal`. A private test file importing this module confirmed that
`inferInstance` proves `(inertiaGroup K A).Normal` for arbitrary `K`, `L`, `A` and that the
quotient `decompositionGroup K A ⧸ inertiaGroup K A` then receives a `Group` instance.
The development check of the module reported no errors or warnings and only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Original source and adaptation

The original is Naganori Yamaguchi (assisted by OpenAI Codex), *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean#L58-L62),
lines 58–62 (docstring at 58, instance signature at 59–60, proof at 61–62), with the
section variables at line 32. The source file (752 lines) has SHA-256
`320e356ad4e05be6714d7db6af8ff9c73cb4e3b40f29b59de1cafc597ba8e913`.

| Original | Adapted |
| --- | --- |
| M239.005, `instance RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal` | `theorem Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal` followed by `attribute [instance] inertiaGroup_normal` |
| Section variables (line 32) and binder `A` (line 59) | Introduced by `intro K L _ _ _ A` |
| `rw [← residueAction_ker (K := K) A]` (line 61) | `change (MonoidHom.ker (residueAction K A)).Normal` |
| `infer_instance` (line 62) | Unchanged |
| Six Mathlib imports (lines 7–12) | The single import of the published statement module |
| `noncomputable section` | Omitted |

The source rewrites with its theorem `residueAction_ker` (M239.004), whose own proof is
`rfl`. Instead of importing a proof of M239.004 (published separately in the sibling module
`ResidueActionKerProof`, not yet in the Library when this module was written) or repeating
that theorem, this module performs the same definitional identification with `change`. The
resulting goal and the final `infer_instance` step are those of the source. The docstring
is kept verbatim. Worker 122 made this adaptation on 14 November 2026; the Lean header
records it.

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Consumers

In the source the instance gives the group structure on
`decompositionGroup K A ⧸ inertiaGroup K A` used later in `ValuationSubring.lean` and in
`ResidueExactSequence.lean` (M243), and it is applied by name at `ValuationSubring.lean`
line 419. Consumers obtain the instance by importing this module.

## Attribution and license

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0 notice
and authorship (assisted by OpenAI Codex), followed by the modification record. The
Library's [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
