# Valuation-subring decomposition data: statement targets M239.004, M239.005 and M239.038

This module states three source units from Naganori Yamaguchi's *ClassFieldTheory (NYLL)*
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean):

| Source unit | Source lines | Source declaration | Statement target |
| --- | --- | --- | --- |
| M239.004 | 53–56 | theorem `residueAction_ker` | `def residueAction_kerStatement` |
| M239.005 | 58–62 | instance `inertiaGroup_normal` | `abbrev inertiaGroup_normalStatement` |
| M239.038 | 368–374 | instance `decompositionField_isGalois` | `abbrev decompositionField_isGaloisStatement` |

The targets are in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Statements`.
Each is a closed proposition: a definition of type `Prop` with universe parameters `u`, `v`
and no other parameters. The module proves nothing. A proof of each target, under the
adapted source name, belongs to a separate proof unit after this module is published.

## Complete propositions

The only import is the M239 data module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`.
The module declares `universe u v`. Inside the namespace above, the three declarations are:

```lean
def residueAction_kerStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    MonoidHom.ker (residueAction K A) = inertiaGroup K A

abbrev inertiaGroup_normalStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    (inertiaGroup K A).Normal

abbrev decompositionField_isGaloisStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : _root_.ValuationSubring L),
    IsGalois (decompositionField K A) L
```

`residueAction`, `inertiaGroup` and `decompositionField` are the published M239
abbreviations of the imported module, in this namespace.

## Mathematical meaning

Let `L / K` be a field extension, `A` a valuation subring of `L`, `D` its decomposition
group (the `K`-automorphisms `σ` of `L` with `σ(A) = A`), `I ≤ D` its inertia group and
`Z = L^D` its decomposition field.

- **M239.004.** The kernel of the residue action `D → Aut(κ(A))` on the residue field
  `κ(A)` of `A` is the inertia group `I`, as a subgroup of `D`. In Mathlib the inertia
  subgroup is defined as this kernel, so the statement records the definition through the
  NYLL wrappers.
- **M239.005.** The inertia group `I` is a normal subgroup of `D`.
- **M239.038.** If `L / K` is finite-dimensional, then `L` is a Galois extension of the
  decomposition field `Z`. Here `↥(decompositionField K A)` is a field and `L` an algebra
  over it through the intermediate-field structures of Mathlib; `IsGalois` is Mathlib's
  predicate (normal and separable). No Galois hypothesis on `L / K` is assumed.

## Original-to-adapted map

The whole source file (752 lines) was read. Its SHA-256 is
`320e356ad4e05be6714d7db6af8ff9c73cb4e3b40f29b59de1cafc597ba8e913`, the value
recorded for M239 in the
[port inventory](../../../../../../notes/reuse/nyll-public-port/m217-m240.md#m239).

| Original lines | Original content | Adapted form |
| --- | --- | --- |
| 1–5 | Copyright and author header | Kept verbatim. A modification note follows it in the same comment. |
| 7–12 | Six Mathlib imports | Replaced by the published M239 data module (Worker 215's artifact `0e135fc0-425a-4406-a36e-f4d889e42935`), which imports `Mathlib.FieldTheory.Galois.Basic` and `Mathlib.RingTheory.Valuation.RamificationGroup` (two of the six), and supplies `residueAction`, `inertiaGroup` and `decompositionField`. The three targets need nothing from the other four imports. |
| 14–21 | Module docstring | Replaced by a docstring describing the three targets. |
| 23, 29–30, 748–749, 752 | `namespace RamificationTheory`, nested namespaces and their ends | The same namespaces with the prefix `Langlands.NYLL`. |
| 25, 751 | `noncomputable section` … `end` | Omitted. A `Prop` has no computational content. |
| 27 | `universe u v` | Unchanged. |
| 32 | `variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` | The first binders of each `∀`, same order, names, universes and binder kinds. |
| 53, 58, 368–370 | Docstrings | Adapted to describe the targets. |
| 54–55 | `theorem residueAction_ker (A : _root_.ValuationSubring L) : MonoidHom.ker (residueAction K A) = inertiaGroup K A` | `residueAction_kerStatement`: the name gets the suffix `Statement`; the binder `A` and the conclusion follow the section binders unchanged. |
| 56 | Proof `by rfl` | Omitted; later proof unit. |
| 59–60 | `instance inertiaGroup_normal (A : _root_.ValuationSubring L) : (inertiaGroup K A).Normal` | `inertiaGroup_normalStatement`, as an `abbrev` (see below), with the same binder and conclusion. The `instance` keyword is not kept, because a statement target is not an instance. |
| 61–62 | Proof by rewriting with `residueAction_ker` and `infer_instance` | Omitted; later proof unit. |
| 371–373 | `instance decompositionField_isGalois [FiniteDimensional K L] (A : _root_.ValuationSubring L) : IsGalois (decompositionField K A) L` | `decompositionField_isGaloisStatement`, as an `abbrev`, keeping `[FiniteDimensional K L]` before `A`. |
| 374 | Proof `IsGalois.of_fixed_field L (decompositionGroup K A)` | Omitted; later proof unit. |
| all other lines | Other M239 rows | Omitted. M239.001–.003 and .011 are in the imported data module; the rest are outside this task. |

### Elaborated telescopes

A source theorem or instance quantifies the section variables it uses, in declaration
order, before its own binders. For all three declarations these are all five section
variables, because `K`, `L` and the three instances are needed to form
`decompositionGroup K A`. The body of each target is the elaborated source type with the
automatic universe names `u_1`, `u_2` replaced by `u`, `v`. `K` remains explicit and `L`
implicit, so a proof `h` of a target is applied as `h K A` (or, for M239.038, with the
`FiniteDimensional` instance found by unification and instance search), exactly like the
source declaration.

### Why two targets are `abbrev`s

The source declarations M239.005 and M239.038 are Prop-valued instances. Their later
proofs must be registered as instances, as in the source. With `abbrev`, the target is
reducible, so a theorem whose type is the target can be given `attribute [instance]` and
is then used by instance search. A private check confirmed this mechanism with the
analogous `abbrev` targets of the M243 statement module. The theorem M239.004 has a plain
`def` target, the usual form for theorem rows.

## Private fidelity checks

The project Lean service (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no errors and no
warnings. Printing the declarations shows each as a definition of type `Prop` with universe
parameters `u`, `v`, the two `abbrev`s with the `@[reducible]` attribute. A private draft,
not part of this contribution, contained verbatim copies of the source declarations at
lines 32–62, 152–156 and 368–374 in a separate namespace. It compiled, and Lean accepted:

1. `example : T.{u, v} := @source` for each target `T` and its source declaration, so the
   source proofs prove the targets.
2. `example : T.{u, v} = type_of% @source.{u, v} := rfl` for each target, so the targets
   are definitionally the source types.

These checks support the correspondence with the source and indicate one proof route. They
do not prove the targets.

## Reuse search

Mathlib defines `ValuationSubring.inertiaSubgroup` as the kernel of
`MulSemiringAction.toRingAut`, which makes M239.004 true by `rfl` and gives M239.005 through
Mathlib's kernel normality instance after rewriting. Mathlib's `IsGalois.of_fixed_field`
states `IsGalois (FixedPoints.subfield G E) E` for a finite group `G`, which the source
proof of M239.038 uses at a fixed field. None of these Mathlib declarations has the NYLL
wrapper form, and since `ValuationSubring.inertiaSubgroup` is not reducible, instance search
does not find `(inertiaGroup K A).Normal` from Mathlib alone. The Library has no
declaration with these targets' names. Task searches for M239, M241 and M243 found no task
other than this one.

## Dependencies and consumers

The module depends only on the published M239 data module. In the source,
`inertiaGroup_normal` provides the group structure on the quotients
`decompositionGroup K A ⧸ inertiaGroup K A` used later in `ValuationSubring.lean` (for
example line 721) and in `ResidueExactSequence.lean` (line 439), and it is applied by name
at `ValuationSubring.lean` line 419. `decompositionField_isGalois` is registered before the
finite-dimensional declarations over `decompositionField K A` that follow it in
`ValuationSubring.lean`. The proofs of the three targets are separate later units of this
task.

## Provenance, license and authorship

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
followed by the source path above. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The source used
Lean 4.35.0-rc2 with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The port
inventory records “none in patch10” for M239, and no compatibility edit was needed. The
Library's `notes/errata` directory has no entry for this source.

The original header is kept verbatim: copyright 2026 Naganori Yamaguchi
([upstream author](https://github.com/n-yamaguchi-0729)), all rights reserved; Apache-2.0;
authors Naganori Yamaguchi (assisted by OpenAI Codex). The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. NOTICE does not
list `ValuationSubring.lean` among its third-party files.

Worker 121 extracted these targets, ran the checks above and wrote this companion on
13 November 2026. The Lean header records the modifications.
