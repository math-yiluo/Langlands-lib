# M337.006: unique solution of the scalar coefficient equation

This module proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.existsUnique_one_sub_uniformizer_pow_mul_eqStatement`
of
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.Statements`
as the theorem

`Langlands.NYLL.LubinTate.SameUniformizer.existsUnique_one_sub_uniformizer_pow_mul_eq`.

For a field `K`, a `LocalField.{u, v} K` structure `F`, a uniformizer
`π : F.valuationSubring` of the chosen valuation
(`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`), a natural number `r`
with `hr : r ≠ 0`, and `b : F.valuationSubring`, it shows that there is a
unique `x : F.valuationSubring` with `(1 - π ^ r) * x = b`. The theorem's binders
are those of the target, and its type is the target applied to `hπ`, `hr` and `b`.

## Source and attribution

The original is NYLL M337.006, lines 77–84 of
`Nyll/ClassFieldTheory/LubinTate/FormalModule/CoefficientEquation.lean` in
Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`87df634a8db769fcf0684ed48933bb957d27a2f8c21e1f50cd58565395933f65`), readable in
registered source `external-lean-reuse-snapshots-2026-10-21` under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`. The Lean file keeps the original
copyright, Apache-2.0 and author header; `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` apply. Worker 485 made the adaptations below.

## Implemented proof

The module imports the M337.004 proof module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U004.Proofs`.
The proof is the term

`(IsUnit.isUnit_iff_mulLeft_bijective.mp (isUnit_one_sub_uniformizer_pow hπ hr)).existsUnique b`.

1. `isUnit_one_sub_uniformizer_pow hπ hr` (M337.004) says that `1 - π ^ r` is
   a unit of the valuation subring.
2. Mathlib's `IsUnit.isUnit_iff_mulLeft_bijective` turns this into
   bijectivity of left multiplication `fun x => (1 - π ^ r) * x`.
3. Mathlib's `Function.Bijective.existsUnique` applied to `b` gives the unique
   preimage `∃! x, (1 - π ^ r) * x = b`. The target unfolds to this
   proposition by definition.

The source proof applies its auxiliary lemma `existsUnique_mul_eq_of_isUnit`
(M337.005, lines 70–75) to the same unit. M337.005 is not ported, as the task
contract requires. Its proof term,
`(IsUnit.isUnit_iff_mulLeft_bijective.mp ha).existsUnique b`, is inlined here
with `ha` instantiated by the M337.004 unit.

## Adaptations

- Extract the theorem into its own module, which imports the M337.004 proof
  module (and through it M337.003, M337.001 and the published statement module).
- Prefix the namespace `LubinTate.SameUniformizer` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` by `Langlands.NYLL`.
- State the theorem's type as the published target applied to `hπ`, `hr` and
  `b`.
- Inline the Mathlib proof term of M337.005 in place of the call to that lemma.
  The source imports `Mathlib.Algebra.Group.Units.Basic` and
  `Mathlib.Logic.Function.Basic` are not repeated, because both Mathlib
  declarations used are available through the published import chain.
- Replace the module documentation; drop the unused `noncomputable section`.
  The docstring is the source docstring.

## Development verification

Worker 485 wrote this module in Task 6067 draft revision 1. Worker 4699
submits it unchanged in Task 6719 after rechecking it against the published
statement module at Library commit `2b8ae82e90fb648bafb921c71a17200990d467af`:
it compiled with no warnings or errors in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), and the theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`. Compiling it does not
show that it has been accepted or published.
