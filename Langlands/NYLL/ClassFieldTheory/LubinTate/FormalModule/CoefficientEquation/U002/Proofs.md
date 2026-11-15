# M337.002: zero residue implies divisibility by the uniformizer

This module proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_dvd_of_residueMap_eq_zeroStatement`
of
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.Statements`
as the theorem

`Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_dvd_of_residueMap_eq_zero`.

For a field `K`, a `LocalField.{u, v} K` structure `F`, a uniformizer
`π : F.valuationSubring` of the chosen valuation
(`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`), and an element
`a : F.valuationSubring` with `ha : F.residueMap a = 0`, it shows that `π ∣ a`
in the valuation subring. The theorem's binders are those of the target, and its type
is the target applied to `hπ` and `ha`.

## Source and attribution

The original is NYLL M337.002, lines 40–50 of
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

The proof follows the source tactic proof step by step:

1. `hmem : a ∈ F.maximalIdeal` follows from `ha` by
   `(IsLocalRing.residue_eq_zero_iff a).1`, replacing the source lemma
   `F.toCompleteDVF.residue_eq_zero_iff` (M107.019).
2. `hspan : a ∈ Ideal.span {π}` is obtained by `simpa` from `hmem`, rewriting
   the maximal ideal with Mathlib's
   `Valuation.IsUniformizer.is_generator (v := F.toCompleteDVF.valuation) hπ`
   (the maximal ideal of the valuation subring is `Ideal.span {π}`). This
   replaces the source lemma
   `F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ` (M107.024).
3. `Ideal.mem_span_singleton.mp hspan` gives `π ∣ a`. This closes the goal,
   which is the target and unfolds to `π ∣ a` by definition.

## Adaptations

- Extract the theorem into its own module, which imports only the published
  statement module.
- Prefix the namespace `LubinTate.SameUniformizer` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` by `Langlands.NYLL`.
- State the theorem's type as the published target applied to `hπ` and `ha`.
- Replace M107.019 and M107.024 by the Mathlib terms above.
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
