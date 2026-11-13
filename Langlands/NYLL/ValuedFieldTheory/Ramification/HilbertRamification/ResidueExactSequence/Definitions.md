# The residue-action exact sequence: fixed-subring data (M243.001–M243.006)

This module adapts the first six data declarations, the source units M243.001–M243.006,
from Naganori Yamaguchi's *ClassFieldTheory (NYLL)* at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. They are in
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L42-L94),
lines 42–94. The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`
declares, in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`:

| Source unit | Source line | Kind | Adapted declaration |
| --- | --- | --- | --- |
| M243.001 | 44 | `abbrev` | `decompositionFixedSubring` |
| M243.002 | 48 | `abbrev` | `decompositionFixedMaximalIdeal` |
| M243.003 | 53 | `abbrev` | `decompositionResidueField` |
| M243.004 | 57 | `abbrev` | `selectedResidueField` |
| M243.005 | 61 | `abbrev` | `decompositionFieldValuationSubring` |
| M243.006 | 68 | `def` | `decompositionFieldValuationSubringEquivFixedSubring` |

The reducibility of each declaration is that of the source. The module proves no theorem;
the only proofs in it are the source's proof fields of the ring equivalence M243.006. The
Prop-valued instances and the theorem of M243 that the later data need are statement
targets in the sibling module `ResidueExactSequence/Statements.lean`. The data rows whose
bodies need such a proof (M243.018 `decompositionFieldResidueEquiv`, M243.020
`decompositionResidueField.instField`, M243.021 `selectedResidueField.instAlgebra`,
M243.023 `decompositionGroupToMaximalIdealStabilizer` and M243.024
`decompositionGroupResidueAction`) are not in this module; they follow the published
proofs they need.

## Complete declarations

The imports are the published M239 data module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`,
`Mathlib.FieldTheory.Galois.Infinite`, `Mathlib.FieldTheory.Galois.Profinite` and
`Mathlib.RingTheory.Invariant.Profinite`. Inside
`namespace Langlands.NYLL.RamificationTheory`, a `noncomputable section`, `universe u v`
and the nested namespaces `HilbertRamification` and `ValuationSubring`, the module has the
source's two section variable lines and these declarations, with the source docstrings:

```lean
variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

abbrev decompositionFixedSubring (A : _root_.ValuationSubring L) : Subring A :=
  FixedPoints.subring A (decompositionGroup K A)

abbrev decompositionFixedMaximalIdeal (A : _root_.ValuationSubring L) :
    Ideal (decompositionFixedSubring K A) :=
  (IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype

abbrev decompositionResidueField (A : _root_.ValuationSubring L) :=
  decompositionFixedSubring K A ⧸ decompositionFixedMaximalIdeal K A

abbrev selectedResidueField (A : _root_.ValuationSubring L) :=
  IsLocalRing.ResidueField A

abbrev decompositionFieldValuationSubring
    (A : _root_.ValuationSubring L) :
    _root_.ValuationSubring (decompositionField K A) :=
  A.comap (decompositionField K A).val

def decompositionFieldValuationSubringEquivFixedSubring
    (A : _root_.ValuationSubring L) :
    decompositionFieldValuationSubring K A ≃+*
      decompositionFixedSubring K A where
  toFun z := ⟨⟨((z : decompositionField K A) : L), z.property⟩, _⟩
  invFun r := ⟨⟨((r : A) : L), _⟩, r.val.property⟩
  left_inv z := by ext; rfl
  right_inv r := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
```

The two membership proofs, shown as `_` above, are the source's tactic proofs, kept
unchanged in the Lean file. The forward proof shows that `z` is fixed by every element of
the decomposition group, from `IntermediateField.mem_fixedField_iff`; the inverse proof
shows that a fixed element of `A` lies in the fixed field, by the same lemma.

### Elaborated signatures

Lean includes a section variable in a definition only when the definition uses it, and
none of these six bodies uses `[IsGalois K L]`. So, exactly as in the source, no
declaration of this module has a Galois hypothesis, although the line
`variable [IsGalois K L]` is kept. `selectedResidueField` does not use `K` either. The
elaborated types, printed with `#check` (universe parameters written `u`, `v` instead of
`u_1`, `u_2`, and instance binder names dropped), are

```text
decompositionFixedSubring : (K : Type u) → {L : Type v} → [Field K] → [Field L] →
  [Algebra K L] → (A : ValuationSubring L) → Subring ↥A
decompositionFixedMaximalIdeal : (K : Type u) → {L : Type v} → [Field K] → [Field L] →
  [Algebra K L] → (A : ValuationSubring L) → Ideal ↥(decompositionFixedSubring K A)
decompositionResidueField : (K : Type u) → {L : Type v} → [Field K] → [Field L] →
  [Algebra K L] → ValuationSubring L → Type v
@selectedResidueField : {L : Type v} → [Field L] → ValuationSubring L → Type v
decompositionFieldValuationSubring : (K : Type u) → {L : Type v} → [Field K] → [Field L] →
  [Algebra K L] → (A : ValuationSubring L) → ValuationSubring ↥(decompositionField K A)
decompositionFieldValuationSubringEquivFixedSubring : (K : Type u) → {L : Type v} →
  [Field K] → [Field L] → [Algebra K L] → (A : ValuationSubring L) →
    ↥(decompositionFieldValuationSubring K A) ≃+* ↥(decompositionFixedSubring K A)
```

`selectedResidueField` has the single universe parameter of `L`. Both residue-field types
are in `Type v`, the universe of `L`, as in the source.

## Mathematical meaning

Let `L / K` be a field extension, `A` a valuation subring of `L` with maximal ideal
`𝔪_A`, `D` its decomposition group and `Z = L^D` its decomposition field (M239). `D` acts
on `A` by ring automorphisms through Mathlib's instance
`ValuationSubring.decompositionSubgroupMulSemiringAction`.

- `decompositionFixedSubring K A` is the subring `A^D` of `A` of elements fixed by every
  element of `D` (Mathlib's `FixedPoints.subring`).
- `decompositionFixedMaximalIdeal K A` is the ideal `𝔪_A ∩ A^D` of `A^D`, the preimage of
  `𝔪_A` under the inclusion `A^D → A`. Whether it is maximal is the statement target
  M243.016, which assumes `L / K` Galois.
- `decompositionResidueField K A` is the quotient ring `A^D ⧸ (𝔪_A ∩ A^D)`, the base
  residue field `κ` of the source's exact sequence. A field structure on it is the later
  instance M243.020.
- `selectedResidueField A` is the residue field `λ = A ⧸ 𝔪_A`.
- `decompositionFieldValuationSubring K A` is the valuation subring `A ∩ Z` of `Z`, the
  preimage of `A` under the inclusion `Z → L`.
- `decompositionFieldValuationSubringEquivFixedSubring K A` is the ring isomorphism
  `A ∩ Z ≃+* A^D` that is the identity on underlying elements of `L`. Both sides consist
  of the elements of `A` fixed by `D`.

## Original-to-adapted map

The whole source file (461 lines) was read. Its SHA-256 is
`cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`, the value
recorded for M243 in the
[port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

| Original lines | Original content | Adapted form |
| --- | --- | --- |
| 1–5 | Copyright and author header | Kept verbatim. A modification note follows it in the same comment. |
| 7 | `import Nyll.ValuedFieldTheory.Ramification.ClosedSubgroups` | Replaced by the published M239 data module and `Mathlib.FieldTheory.Galois.Infinite`. `ClosedSubgroups.lean` imports `RamificationGroup.lean` (which imports only `ValuationSubring.lean`) and `Mathlib.FieldTheory.Galois.Infinite`; these six declarations use only the M239 abbreviations from that chain. |
| 8 | `import Nyll.ValuedFieldTheory.Ramification.ProfiniteInvariant` | Replaced by its two imports, `Mathlib.FieldTheory.Galois.Profinite` and `Mathlib.RingTheory.Invariant.Profinite`. No declaration of this module uses M242. |
| 10–24 | Module docstring on the exact sequence | Replaced by a docstring describing the six data declarations. |
| 26, 34–35, 456–457, 461 | `namespace RamificationTheory`, nested namespaces and their ends | The same namespaces with the prefix `Langlands.NYLL`. |
| 30, 32, 459 | `noncomputable section`, `universe u v`, `end` | Unchanged. |
| 37 | `open scoped Pointwise Topology` | Omitted. These declarations use neither notation. |
| 39–40 | `variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]`, `variable [IsGalois K L]` | Unchanged. |
| 42–94 | M243.001–M243.006 with docstrings and proofs | Unchanged. |
| 96–454 | M243.007 onwards | Omitted here. M243.007, .013, .014, .016, .019 and .022 are statement targets in `ResidueExactSequence/Statements.lean`; the remaining rows of the task follow later; the rest of the file is outside this task. |

### The pinned import chain

The source file's NYLL import closure contributes only Mathlib modules and NYLL
declarations. The two NYLL imports are replaced by the published M239 module plus three
Mathlib modules: `Mathlib.FieldTheory.Galois.Infinite`, imported by `ClosedSubgroups.lean`,
and the two imports of `ProfiniteInvariant.lean`. The M239 module is Worker 215's
artifact `0e135fc0-425a-4406-a36e-f4d889e42935`. It imports
`Mathlib.FieldTheory.Galois.Basic` and `Mathlib.RingTheory.Valuation.RamificationGroup`,
two of the six Mathlib imports of `ValuationSubring.lean`. This module compiles with these
imports. It does not claim that its import closure equals that of the source.

## Private fidelity checks

The project Lean service (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no errors and no
warnings. A private draft, not part of this contribution, contained verbatim copies of
the source declarations at lines 39–94 in a separate namespace, on top of verbatim copies of
the M239 abbreviations. It compiled, and Lean accepted, for each of the six declarations,
`@adapted.{u, v} = @source.{u, v} := rfl` (for `selectedResidueField`, `.{v}`). The
`#check` output above is the same, binder by binder, as that of the verbatim copies.

## Reuse search

`FixedPoints.subring`, `Ideal.comap`, `ValuationSubring.comap` and
`IsLocalRing.ResidueField` are Mathlib's and are used directly. The declarations here only
name particular instances of them, and the NYLL consumers (Task 5264's M249, M250, M252)
use these names. `FixedPoints.subring` is defined in
`Mathlib/Algebra/Algebra/Subalgebra/Operations.lean` and used elsewhere in Mathlib only in
`Mathlib/RingTheory/Invariant/Basic.lean`; neither file has a ring equivalence with a
`ValuationSubring.comap`, so M243.006 has no Mathlib counterpart. The Library has no declaration with these names, and task
searches for M243 found no task other than this one.

## Dependencies and consumers

The module depends on the published M239 data module and Mathlib. It is imported by
`ResidueExactSequence/Statements.lean`. In the source, every later declaration of
`ResidueExactSequence.lean` uses these data, and the local-reciprocity files named in the
task context use `decompositionFieldValuationSubring`, `decompositionResidueField` and
`selectedResidueField`.

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

Worker 121 extracted these declarations, ran the checks above and wrote this companion on
13 November 2026. The Lean header records the modifications.
