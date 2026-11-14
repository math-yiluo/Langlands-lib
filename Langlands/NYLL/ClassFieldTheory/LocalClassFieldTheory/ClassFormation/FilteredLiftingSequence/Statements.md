# NYLL recursive correction sequences: statements

Worker 111 adapts the theorem units M151.002, M151.003, M151.008, M151.010,
M151.011 and M151.012 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
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

| Unit | Original theorem in `LocalClassFieldTheory` | Source lines (docstring through proof; statement) | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M151.002 | `filteredCorrectionProduct_zero` | 33–37; 35–36 | `filteredCorrectionProduct_zeroStatement` |
| M151.003 | `filteredCorrectionProduct_succ` | 39–44; 41–43 | `filteredCorrectionProduct_succStatement` |
| M151.008 | `chosenFilteredLiftStateSequence_zero` | 91–99; 93–98 | `chosenFilteredLiftStateSequence_zeroStatement` |
| M151.010 | `chosenFilteredLiftCorrectionSequence_mem` | 113–122; 114–120 | `chosenFilteredLiftCorrectionSequence_memStatement` |
| M151.011 | `chosenFilteredLiftStateSequence_equation` | 124–134; 125–132 | `chosenFilteredLiftStateSequence_equationStatement` |
| M151.012 | `filteredLift_initial_eq_correctionProduct_mul_state` | 136–155; 138–146 | `filteredLift_initial_eq_correctionProduct_mul_stateStatement` |

## Meaning

All six propositions are about the generic data of the M151 data module; no
field, valuation, Galois group or cohomology occurs.

- M151.002: for a monoid `A` and `z : Nat → A`,
  `filteredCorrectionProduct z 0 = 1`.
- M151.003: for a monoid `A`, `z : Nat → A` and `d : Nat`,
  `filteredCorrectionProduct z (d + 1) = filteredCorrectionProduct z d * z d`.

The remaining four share the data of a commutative group `A`, a predicate
family `P : Nat → A → Prop` (filtration levels), a predicate `R : A → Prop`
(the condition preserved by lifting), a monoid endomorphism `F : A →* A`, a
base depth `n : Nat`, an initial state `initial : FilteredLiftState A P R n 0`
and a hypothesis `step` that every state at every relative depth `i` admits
some one-step lift `FilteredLiftStep A P R F n i s`. Write `a_i` for the
`value` of `chosenFilteredLiftStateSequence A P R F n initial step i` and
`b_i` for `chosenFilteredLiftCorrectionSequence A P R F n initial step i`.

- M151.008: `chosenFilteredLiftStateSequence A P R F n initial step 0 = initial`
  (an equality of states, not only of values).
- M151.010: for every `i : Nat`, `P (n + i) b_i`: the chosen correction at
  relative depth `i` lies in filtration level `n + i`.
- M151.011: for every `i : Nat`, `a_i = F b_i * a_(i+1)`.
- M151.012: for every `d : Nat`,
  `initial.value = F (filteredCorrectionProduct (fun i => b_i) d) * a_d`, that
  is the initial remainder is `F (b_0 * ⋯ * b_(d-1))` times the depth-`d`
  remainder. The source writes the correction sequence as the partially
  applied `chosenFilteredLiftCorrectionSequence A P R F n initial step`, which
  the target keeps verbatim.

## Telescopes

The universe is `u` (source line 26). The source section has no `variable`
command, so every binder is the theorem's own; the adapted definitions keep
them in source order and with source binder kinds:

```lean
-- M151.002
filteredCorrectionProduct_zeroStatement {A : Type u} [Monoid A] (z : Nat → A) : Prop
-- M151.003
filteredCorrectionProduct_succStatement {A : Type u} [Monoid A]
    (z : Nat → A) (d : Nat) : Prop
-- M151.008 (no further binder), M151.010 and M151.011 (then `(i : Nat)`),
-- M151.012 (then `(d : Nat)`)
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s))
```

Each body is copied verbatim from the source statement lines listed above
(36, 43, 98, 119–120, 130–132 and 143–146). Every binder occurs in its
proposition or in the type of a later binder, so no linter option is needed.

## Reused declarations

`filteredCorrectionProduct` (M151.001), `FilteredLiftState` (M151.004),
`FilteredLiftStep` (M151.005), `chosenFilteredLiftStateSequence` (M151.006)
and `chosenFilteredLiftCorrectionSequence` (M151.007), all in
`Langlands.NYLL.LocalClassFieldTheory`, come from the published module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FilteredLiftingSequence.Definitions`,
the verbatim namespaced port of the same source file's data. `Monoid`,
`CommGroup`, `MonoidHom` (`A →* A`) and its coercion to functions come from
Mathlib through that module's import `Mathlib.Algebra.Group.Hom.Defs`.

## Modifications

- The namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`.
- Each theorem becomes a `Prop`-valued `def` with the suffix `Statement`
  whose body is exactly the source statement. The source proofs (`rfl`
  for M151.002, .003 and .008; the `correction_mem` and `equation` fields of
  the chosen step for M151.010 and .011; an induction on `d` for M151.012) are
  not ported here. Proofs of these targets are separate `lean.proof@1` work.
- The `@[simp]` attributes of M151.002, .003 and .008 are dropped: they
  belong to the theorems, not to `Prop`-valued definitions.
- The source import
  `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct`
  is replaced by the published M151 data module, which supplies every
  constant the six targets mention.
- Docstrings are rewritten to name each unit and describe its proposition.
- M151.009 (`chosenFilteredLiftStateSequence_succ`, lines 101–111) is not in
  this task's unit list and is omitted. None of the six targets mentions it;
  the source proof of M151.012 invokes M151.011 rather than M151.009.

No hypothesis is added or removed, no proof is supplied and no instance is
declared. The copyright and author header is retained, followed by a
modification notice. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` in the Library remain applicable. These statements
prove no class-formation or reciprocity theorem.
