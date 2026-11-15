# M337.004: the factor `1 - π ^ r` is a unit

This module proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.isUnit_one_sub_uniformizer_powStatement`
of
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.Statements`
as the theorem

`Langlands.NYLL.LubinTate.SameUniformizer.isUnit_one_sub_uniformizer_pow`.

For a field `K`, a `LocalField.{u, v} K` structure `F`, a uniformizer
`π : F.valuationSubring` of the chosen valuation
(`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`) and a natural number
`r` with `hr : r ≠ 0`, it shows that `1 - π ^ r` is a unit of the valuation
subring. The theorem's binders are those of the target, and its type is the target
applied to `hπ` and `hr`.

## Source and attribution

The original is NYLL M337.004, lines 59–68 of
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

The module imports the M337.003 proof module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U003.Proofs`.
The proof follows the source tactic proof:

1. `apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits`: in a local ring,
   `1 - a` is a unit when `a` is a nonunit. The goal, the target unfolded by
   definition to `IsUnit (1 - π ^ r)`, becomes `π ^ r ∈ nonunits`, that is,
   `IsUnit (π ^ r) → False`.
2. After `intro hunit`, `(IsLocalRing.residue_ne_zero_iff_isUnit (π ^ r)).2 hunit`
   gives `F.residueMap (π ^ r) ≠ 0`. This replaces the source lemma
   `F.toCompleteDVF.residue_ne_zero_iff_isUnit` (M107.020).
3. This contradicts `residueMap_uniformizer_pow_eq_zero hπ hr` (M337.003).

## Adaptations

- Extract the theorem into its own module, which imports the M337.003 proof
  module (and through it M337.001 and the published statement module).
- Prefix the namespace `LubinTate.SameUniformizer` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` by `Langlands.NYLL`.
- State the theorem's type as the published target applied to `hπ` and `hr`.
- Replace M107.020 by `IsLocalRing.residue_ne_zero_iff_isUnit`.
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
