# NYLL recursive correction sequences: data

Worker 111 adapts the data units M151.001, M151.004, M151.005, M151.006 and
M151.007 from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/FilteredLiftingSequence.lean`
(file SHA-256
`1c31491ae5c87b30d73ddafa35b9ff58e406c9e7967fb50adc48db234e21bd5f`).
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Unit | Original declaration in `LocalClassFieldTheory` | Kind | Source lines (docstring through body) | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- | --- |
| M151.001 | `filteredCorrectionProduct` | def | 28–31 | `filteredCorrectionProduct` |
| M151.004 | `FilteredLiftState` | structure | 46–55 | `FilteredLiftState` |
| M151.005 | `FilteredLiftStep` | structure | 57–68 | `FilteredLiftStep` |
| M151.006 | `chosenFilteredLiftStateSequence` | def | 70–80 | `chosenFilteredLiftStateSequence` |
| M151.007 | `chosenFilteredLiftCorrectionSequence` | def | 82–89 | `chosenFilteredLiftCorrectionSequence` |

## Meaning

The module isolates the dependent-choice bookkeeping of an infinite-product
argument. Everything is generic in a type `A : Type u`; no field, valuation,
Galois group or cohomology occurs.

- `filteredCorrectionProduct z d`, for a monoid `A` and a sequence
  `z : Nat → A`, is the left-to-right product `z 0 * z 1 * ⋯ * z (d - 1)`,
  defined by structural recursion: `1` at `0` and
  `filteredCorrectionProduct z d * z d` at `d + 1`.
- `FilteredLiftState A P R n i`, for a predicate family `P : Nat → A → Prop`
  (membership in filtration level `k`), a predicate `R : A → Prop` (the
  condition preserved by lifting) and depths `n i : Nat`, is a structure with
  fields `value : A`, `mem : P (n + i) value` and `stable : R value`.
- `FilteredLiftStep A P R F n i s`, for a commutative group `A`, a monoid
  endomorphism `F : A →* A` and a state `s` at relative depth `i`, is a
  structure with fields `correction : A`,
  `correction_mem : P (n + i) correction`,
  `next : FilteredLiftState A P R n (i + 1)` and
  `equation : s.value = F correction * next.value`: one step
  `a_i = F(b_i) a_(i+1)`.
- `chosenFilteredLiftStateSequence A P R F n initial step i`, given an initial
  state at relative depth `0` and a hypothesis `step` that every state admits
  some one-step lift, is the state at relative depth `i` defined by recursion
  on `i`: `initial` at `0`, and at `i + 1` the `next` field of
  `Classical.choice` applied to `step i` at the previously chosen state.
- `chosenFilteredLiftCorrectionSequence A P R F n initial step i` is the
  `correction` field of the same chosen step at depth `i`.

The two chosen sequences are noncomputable: they choose one lift per depth
with `Classical.choice`, exactly as the source does.

## Complete interfaces

The shared universe is `u` (source line 26). The source section has no
`variable` command; every binder below is the declaration's own, in source
order and with source binder kinds:

```lean
filteredCorrectionProduct {A : Type u} [Monoid A] (z : Nat → A) : Nat → A

structure FilteredLiftState (A : Type u) (P : Nat → A → Prop)
    (R : A → Prop) (n i : Nat) : Type u

structure FilteredLiftStep (A : Type u) [CommGroup A]
    (P : Nat → A → Prop) (R : A → Prop) (F : A →* A)
    (n i : Nat) (s : FilteredLiftState A P R n i) : Type u

chosenFilteredLiftStateSequence
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) :
    (i : Nat) → FilteredLiftState A P R n i

chosenFilteredLiftCorrectionSequence
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) : A
```

Structure fields, field order, field types, definition bodies, the
equation-compiler recursion and the `noncomputable` markers are copied
verbatim from the source, with the source docstrings.

## Modifications

- The namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`.
- The source import
  `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct`
  is replaced by `Mathlib.Algebra.Group.Hom.Defs`, which supplies `Monoid`,
  `CommGroup` and `MonoidHom`; none of the five declarations uses anything from
  the NYLL import.
- The module docstring is shortened to describe this data-only module.
- The theorem units of the source module (M151.002, M151.003, M151.008,
  M151.009, M151.010, M151.011 and M151.012) are not part of this module and
  no proof is ported here. Their targets are separate `Prop`-valued statement
  work; M151.009 (`chosenFilteredLiftStateSequence_succ`) is not in this
  task's unit list.

No instance is declared, and no hypothesis, field or binder is added or
removed. The copyright and author header is retained, followed by a
modification notice. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` in the Library remain applicable. This data proves no
class-formation or reciprocity theorem.
