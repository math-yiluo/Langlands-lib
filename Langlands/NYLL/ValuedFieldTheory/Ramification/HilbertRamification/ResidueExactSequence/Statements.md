# The residue-action exact sequence: statement targets on the fixed subring

This module states six source units from Naganori Yamaguchi's *ClassFieldTheory (NYLL)*
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean).
Five are Prop-valued instances and one is a theorem:

| Source unit | Source lines | Source declaration | Statement target |
| --- | --- | --- | --- |
| M243.007 | 96–100 | instance `decompositionFixedSubring.instIsLocalRing` | `abbrev decompositionFixedSubring.instIsLocalRingStatement` |
| M243.013 | 165–170 | instance `decompositionFixedSubring.instSMulCommClass` | `abbrev decompositionFixedSubring.instSMulCommClassStatement` |
| M243.014 | 172–177 | instance `decompositionFixedSubring.instIsInvariant` | `abbrev decompositionFixedSubring.instIsInvariantStatement` |
| M243.016 | 202–206 | instance `decompositionFixedMaximalIdeal.instIsMaximal` | `abbrev decompositionFixedMaximalIdeal.instIsMaximalStatement` |
| M243.019 | 228–234 | instance `selectedMaximalIdeal.instLiesOver` | `abbrev selectedMaximalIdeal.instLiesOverStatement` |
| M243.022 | 250–272 | theorem `decompositionGroup_maximalIdeal_stabilizer_eq_top` | `def decompositionGroup_maximalIdeal_stabilizer_eq_topStatement` |

The targets are in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`.
Each is a closed proposition: a definition of type `Prop` with universe parameters `u`, `v`
and no other parameters. The module proves nothing. A proof of each target, under the
adapted source name, belongs to a separate proof unit after this module is published.

## Complete propositions

The only import is the M243 data module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`,
which imports the M239 data module. The module declares `universe u v`. Inside the
namespace above, after `open scoped Pointwise`, the six declarations are:

```lean
abbrev decompositionFixedSubring.instIsLocalRingStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    IsLocalRing (decompositionFixedSubring K A)

abbrev decompositionFixedSubring.instSMulCommClassStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A

abbrev decompositionFixedSubring.instIsInvariantStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A)

abbrev decompositionFixedMaximalIdeal.instIsMaximalStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (A : _root_.ValuationSubring L),
    (decompositionFixedMaximalIdeal K A).IsMaximal

abbrev selectedMaximalIdeal.instLiesOverStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    (IsLocalRing.maximalIdeal A).LiesOver
      (decompositionFixedMaximalIdeal K A)

def decompositionGroup_maximalIdeal_stabilizer_eq_topStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) = ⊤
```

`decompositionGroup` (M239.001), `decompositionFixedSubring` (M243.001) and
`decompositionFixedMaximalIdeal` (M243.002) are the published abbreviations of the
imported modules.

## Mathematical meaning

Let `L / K` be a field extension, `A` a valuation subring of `L` with maximal ideal `𝔪_A`,
`D` the decomposition group of `A`, acting on `A` by ring automorphisms (Mathlib's instance
`ValuationSubring.decompositionSubgroupMulSemiringAction`), `A^D` the fixed subring and
`𝔪_A ∩ A^D` the contracted ideal (M243.001, M243.002). The ring `A^D` acts on `A` by
multiplication through the algebra structure of a subring on its ambient ring.

- **M243.007.** `A^D` is a local ring. (It is isomorphic, by M243.006, to the valuation
  subring `A ∩ Z` of the decomposition field `Z`.)
- **M243.013.** The actions of `D` and of `A^D` on `A` commute: `σ (r x) = r (σ x)` for
  `σ ∈ D`, `r ∈ A^D`, `x ∈ A`.
- **M243.014.** `Algebra.IsInvariant (A^D) A D`: every element of `A` fixed by all of `D`
  is the image of an element of `A^D`.
- **M243.016.** If `L / K` is Galois (possibly infinite), the ideal `𝔪_A ∩ A^D` of `A^D`
  is maximal.
- **M243.019.** `𝔪_A` lies over `𝔪_A ∩ A^D` in Mathlib's sense: `𝔪_A ∩ A^D` equals the
  preimage `Ideal.under (A^D) 𝔪_A` of `𝔪_A` under the algebra map `A^D → A`.
- **M243.022.** Under the pointwise action of `D` on the ideals of `A` (Mathlib's
  `Ideal.pointwiseMulSemiringAction`, scoped in `Pointwise`), the stabilizer of `𝔪_A` is
  all of `D`: every element of the decomposition group maps `𝔪_A` onto itself.

Only M243.016 assumes `L / K` Galois. No hypothesis is added to any target.

## Original-to-adapted map

The whole source file (461 lines) was read. Its SHA-256 is
`cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`, the value
recorded for M243 in the
[port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

| Original lines | Original content | Adapted form |
| --- | --- | --- |
| 1–5 | Copyright and author header | Kept verbatim. A modification note follows it in the same comment. |
| 7–8 | Imports of `ClosedSubgroups` and `ProfiniteInvariant` | Replaced by the published M243 data module, whose Markdown describes the import chain. The targets use only `decompositionGroup`, `decompositionFixedSubring` and `decompositionFixedMaximalIdeal`. |
| 10–24 | Module docstring | Replaced by a docstring describing the six targets. |
| 26, 34–35, 456–457, 461 | `namespace RamificationTheory`, nested namespaces and their ends | The same namespaces with the prefix `Langlands.NYLL`. |
| 30, 459 | `noncomputable section` … `end` | Omitted. A `Prop` has no computational content. |
| 32 | `universe u v` | Unchanged. |
| 37 | `open scoped Pointwise Topology` | `open scoped Pointwise` is kept: it supplies the action of `D` on ideals in M243.022. `Topology` is omitted; no target uses its notation. |
| 39 | `variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` | The first binders of each `∀`, same order, names, universes and binder kinds. |
| 40 | `variable [IsGalois K L]` | Kept, after `[Algebra K L]`, only in M243.016, the only one of the six source declarations whose elaborated type has it (see below). |
| 42–94 | M243.001–M243.006 | In the imported data module. |
| 96–100 | Instance M243.007 `decompositionFixedSubring.instIsLocalRing (A) : IsLocalRing (decompositionFixedSubring K A)` and its one-line proof | Target `decompositionFixedSubring.instIsLocalRingStatement` with the same binder and conclusion; proof omitted. |
| 102–163 | Private theorems M243.008–M243.012 | Omitted. As private rows they will be proved inside the proofs that consume them (M243.013, M243.014 and M243.016) and recorded there. |
| 165–170 | Instance M243.013 `decompositionFixedSubring.instSMulCommClass` | Target `decompositionFixedSubring.instSMulCommClassStatement`; proof omitted. |
| 172–177 | Instance M243.014 `decompositionFixedSubring.instIsInvariant` | Target `decompositionFixedSubring.instIsInvariantStatement`; proof omitted. |
| 179–200 | Private theorem M243.015 `decompositionFixedMaximalIdeal_isMaximal` | Omitted; to be proved inside the proof of M243.016. |
| 202–206 | Instance M243.016 `decompositionFixedMaximalIdeal.instIsMaximal` | Target `decompositionFixedMaximalIdeal.instIsMaximalStatement`, with `[IsGalois K L]`; proof omitted. |
| 208–226 | M243.017 theorem and M243.018 data | Not here. M243.017's statement uses the local-ring instance M243.007, so it is stated after the proof of M243.007 is published; M243.018 needs M243.017's proof. |
| 228–234 | Instance M243.019 `selectedMaximalIdeal.instLiesOver` | Target `selectedMaximalIdeal.instLiesOverStatement`; proof omitted. |
| 236–248 | Instances M243.020 (`Field`) and M243.021 (`Algebra`) | Not here: these are data, built from the proofs of M243.016 and M243.019, and follow those proofs. |
| 250–252 | `omit [IsGalois K L] in` and docstring | The `omit` is reflected by the absence of `[IsGalois K L]` from the target. |
| 253–256 | `theorem decompositionGroup_maximalIdeal_stabilizer_eq_top (A) : MulAction.stabilizer (decompositionGroup K A) (IsLocalRing.maximalIdeal A) = ⊤` | Target `decompositionGroup_maximalIdeal_stabilizer_eq_topStatement`; same binder and conclusion. |
| 257–272 | Proof | Omitted; later proof unit. |
| 274–454 | M243.023 onwards | Not here. M243.023–.025, .029 and .030 follow later in this task; the others are outside it. |

Every docstring was adapted to describe its target. The `instance` keyword is not kept,
because a statement target is not an instance.

### Elaborated telescopes and `[IsGalois K L]`

A source declaration quantifies the section variables it includes, in declaration order,
before its own binders. All six include the five variables of line 39, because their
types use `decompositionGroup K A`. The section instance `[IsGalois K L]` of line 40 is
in the elaborated type only of M243.016. The source declarations show why: the body of
M243.016 uses the private theorem M243.015, which is stated under the section variable
without `omit`; the bodies of M243.007, .013, .014 and .019 do not use it (M243.013 and
M243.014 use private helpers declared with `omit [IsGalois K L] in`); and M243.022 has
`omit [IsGalois K L] in`. The printed source types confirm this, and each target's body
is the elaborated source type with the universe names `u_1`, `u_2` written `u`, `v`. `K`
stays explicit and `L` implicit in every target.

### Why five targets are `abbrev`s

The five source instances must have proofs registered as instances in the same scope,
because later source declarations rely on instance search for them; for example
M243.020 and M243.021 need `IsMaximal` and `LiesOver`, and the profinite results used by
M243.029 and M243.030 need `SMulCommClass` and `Algebra.IsInvariant`. With `abbrev`, the
target is reducible, so a theorem whose type is the target can be given
`attribute [instance]`. A private check confirmed this for M243.007 and M243.019: before
the attribute, `inferInstance` fails for the conclusion at given `K` and `A`; after
`attribute [instance]` on a theorem typed by the target, `inferInstance` succeeds. The
theorem M243.022 has a plain `def` target.

For M243.013 the private check also showed that Mathlib already supplies the instance:
`inferInstance` proves `SMulCommClass (decompositionGroup K A) (decompositionFixedSubring K A) A`
from Mathlib's `instance : SMulCommClass G (FixedPoints.subring B G) B`
(`Mathlib/Algebra/Algebra/Subalgebra/Operations.lean`, line 102), since
`decompositionFixedSubring` is an `abbrev` for `FixedPoints.subring`. Its proof unit
will therefore prove the target and record, instead of registering a second instance,
that Mathlib supplies it. The target is still published so that the row has its adapted
name.

## Private fidelity checks

The project Lean service (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no errors and no
warnings. Printing the declarations shows each as a definition of type `Prop` with universe
parameters `u`, `v`, the five `abbrev`s with the `@[reducible]` attribute. A private draft,
not part of this contribution, contained verbatim copies of the source declarations at
lines 39–413 of `ResidueExactSequence.lean` (M243.001–M243.030), on top of verbatim copies of the M239
declarations and of `ClosedSubgroups.lean` lines 32–81, in a separate namespace, with the
published `ProfiniteInvariant` proof module imported. It compiled, and Lean accepted:

1. `example : T.{u, v} := @source` for each target `T` and its source declaration, so the
   source proofs prove the targets.
2. `example : T.{u, v} = type_of% @source.{u, v} := rfl` for each target, so the targets
   are definitionally the source types.

These checks support the correspondence with the source and indicate one proof route. They
do not prove the targets.

## Reuse search

- M243.013: Mathlib's instance noted above supplies it.
- M243.014: Mathlib has no `Algebra.IsInvariant` instance for `FixedPoints.subring`; the
  instances in `Mathlib/RingTheory/Invariant/` concern other settings.
- M243.019: Mathlib's `Ideal.over_under` instance (`Mathlib/RingTheory/Ideal/Over.lean`)
  states `P.LiesOver (P.under R)`. It is not found by instance search for the target's
  `decompositionFixedMaximalIdeal K A`, which is spelled with `Ideal.comap` along
  `Subring.subtype` (the private check above shows `inferInstance` failing before the
  attribute).
- M243.007, M243.016 and M243.022 concern the NYLL fixed subring and have no Mathlib or
  Library counterpart by name. The source proof of M243.016 uses Mathlib's
  `Algebra.IsInvariant.isIntegral_of_profinite` and
  `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`.

The Library has no declaration with these targets' names, and task searches for M243
found no task other than this one.

## Dependencies and consumers

The module depends on the published M243 and M239 data modules. In the source, these six
declarations are used by the rest of `ResidueExactSequence.lean`: M243.017 applies
M243.016, M243.020 and M243.021 use M243.016 and M243.019, M243.023 uses M243.022, and the
residue action M243.024 with its surjectivity M243.029 and the normality instance M243.030
rely on the instances. Through those, they serve the local-reciprocity consumers named in
the task context.

## Provenance, license and authorship

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
followed by the source path above. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The source used
Lean 4.35.0-rc2 with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The port
inventory records “none in patch10” for M243, and no compatibility edit was needed. The
Library's `notes/errata` directory has no entry for this source.

The original header is kept verbatim: copyright 2026 Naganori Yamaguchi
([upstream author](https://github.com/n-yamaguchi-0729)), all rights reserved; Apache-2.0;
authors Naganori Yamaguchi (assisted by OpenAI Codex). The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged. Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. NOTICE does not
list `ResidueExactSequence.lean` among its third-party files.

Worker 121 extracted these targets, ran the checks above and wrote this companion on
13 November 2026. The Lean header records the modifications.
