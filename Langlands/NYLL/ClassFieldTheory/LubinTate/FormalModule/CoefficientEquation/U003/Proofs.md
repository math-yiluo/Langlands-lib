# M337.003: positive powers of a uniformizer reduce to zero

This module proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.residueMap_uniformizer_pow_eq_zeroStatement`
of
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.Statements`
as the theorem

`Langlands.NYLL.LubinTate.SameUniformizer.residueMap_uniformizer_pow_eq_zero`.

For a field `K`, a `LocalField.{u, v} K` structure `F`, a uniformizer
`π : F.valuationSubring` of the chosen valuation
(`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`) and a natural number
`r` with `hr : r ≠ 0`, it shows that `F.residueMap (π ^ r) = 0`. The theorem's binders
are those of the target, and its type is the target applied to `hπ` and `hr`.

## Source and attribution

The original is NYLL M337.003, lines 52–57 of
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

The module imports the M337.001 proof module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U001.Proofs`.

1. `h0 : F.residueMap π = 0` is
   `residueMap_uniformizer_eq_zero hπ` (M337.001). The theorem's type is that
   target, which unfolds to this equation by definition.
2. `simp` with the target definition, `map_pow`, `h0` and `hr` unfolds the
   target, rewrites `F.residueMap (π ^ r)` as `(F.residueMap π) ^ r = 0 ^ r`, and
   closes `0 ^ r = 0` using `r ≠ 0`.

This is the source proof `simp [map_pow, residueMap_uniformizer_eq_zero hπ, hr]`.
The M337.001 equation is first named as a hypothesis, and the target
definition is added to the simp set.

## Adaptations

- Extract the theorem into its own module, which imports the M337.001 proof
  module and, through it, the published statement module.
- Prefix the namespace `LubinTate.SameUniformizer` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` by `Langlands.NYLL`.
- State the theorem's type as the published target applied to `hπ` and `hr`.
- Name the M337.001 equation as `h0` and add the target definition to the simp
  set, as described above.
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
