# Uniqueness of the chosen valuation ring of the separable closure: proof of M249.009

The theorem
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension`
has exactly the closed published type
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtensionStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U009.Statements`).
It has no universe parameters and no further arguments.

For every nonarchimedean local field `K : Type` (with its `Field`,
`ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField`
instances) and every valuation subring `B` of `SeparableClosure K` such that
`(localCompleteDVF K).valuation.HasExtension B.valuation`, it proves
`localSeparableValuationSubring K = B`. So every valuation ring of the
separable closure whose valuation extends the canonical valuation of `K` is
the ring chosen in M249.006. The choice therefore does not depend on the
Chevalley extension behind it. The statement and every module it imports
are unchanged.

## The implemented proof

1. **Pullback (source M249.007, with the private M249.004 inlined).** A
   local `have hpullback` proves, for every `x : K`, that
   `algebraMap K (SeparableClosure K) x` lies in
   `(localSeparableValuationSubring K).toSubring` exactly when `x` lies in
   `(localCompleteDVF K).valuation.valuationSubring`. The third component of
   `Classical.choose_spec` of the published Chevalley theorem
   `exists_extension_valuationSubring` (with `L := AlgebraicClosure K`)
   gives this equivalence for `AlgebraicClosure K`. By definition,
   `localSeparableValuationSubring K` is the preimage of
   `PortInternal.M249.d003 K` (that `Classical.choose`) under
   `SeparableClosure K → AlgebraicClosure K`. A `change` exposes this, and
   `IsScalarTower.algebraMap_apply` for the tower
   `K → SeparableClosure K → AlgebraicClosure K` rewrites the composite map.
   The algebra and tower here are the published `PortInternal.M249.d001`
   and `d002`, enabled with `attribute [local instance]` because they are
   local instances in their own module.
2. **Extension (source M249.008).** The published
   `hasExtension_valuation_of_valuationSubring_pullback`, applied to
   `hpullback`, gives a local
   `(localCompleteDVF K).valuation.HasExtension
   (localSeparableValuationSubring K).valuation`.
3. **Reduction to one element.** After `ext z`, let `E` be the
   intermediate field `IntermediateField.adjoin K {z}` of
   `SeparableClosure K / K`. It is finite-dimensional over `K` by
   `IntermediateField.adjoin.finiteDimensional` applied to
   `Algebra.IsIntegral.isIntegral z`, and separable by instance inference.
   Let `Ares` and `Bres` be the published `restrictIntermediateField`
   restrictions of the chosen ring and of `B` to `E`. By the published
   `restrictIntermediateField_hasExtension`, the valuation of each extends
   `(localCompleteDVF K).valuation`.
4. **Finite-separable uniqueness.** The published
   `chosenLocalExtension_uniqueValuationExtension.{0}`, applied to `K`, `E`
   and `Ares.valuation`, and again to `Bres.valuation`, shows that each is
   equivalent to `(chosenLocalExtensionCompleteDVF K E).valuation`. So
   `Ares.valuation.IsEquiv Bres.valuation` (by `symm` and `trans`).
   Mathlib's `Valuation.isEquiv_iff_valuationSubring` turns this into
   equality of the valuation subrings of the two valuations, and
   `ValuationSubring.valuationSubring_valuation` (applied twice) gives
   `Ares = Bres`.
5. **Conclusion.** With `zE : E` the element `z`, which lies in `E` by
   `IntermediateField.subset_adjoin`, membership of `z` in each ring is by
   definition membership of `zE` in its restriction. The goal
   `zE ∈ Ares ↔ zE ∈ Bres` follows from `rw [hAB]`.

The development check in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
reports 0 errors and 0 warnings. The theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Dependencies

| Role | Declaration | Module |
| --- | --- | --- |
| target | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtensionStatement` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U009.Statements` |
| M249.006 and local instances M249.001–.003 (through the statement module) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring`, `Langlands.NYLL.PortInternal.M249.d001`, `d002`, `d003` | `...LocalReciprocity.LocalResidueDatum.U006.Definitions` |
| M110.003 (through the M249.006 module) | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring` | `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U003.Proofs` |
| M110.004 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback` | `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U004.Proofs` |
| M233.004 | `Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField` | `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.RestrictIntermediateField` |
| M233.007 | `Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension` | `...FiniteLevelValuationRestriction.U007.Proofs` |
| M248.011, closed specialization | `Langlands.NYLL.LocalFieldTheory.chosenLocalExtension_uniqueValuationExtension` (with `chosenLocalExtensionCompleteDVF`) | `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenUniquenessProof` |

The Mathlib declarations used are `Classical.choose_spec`,
`IsScalarTower.algebraMap_apply`, `IntermediateField.adjoin`,
`IntermediateField.adjoin.finiteDimensional`,
`Algebra.IsIntegral.isIntegral`, `IntermediateField.subset_adjoin`,
`Valuation.IsEquiv.symm`, `Valuation.IsEquiv.trans`,
`Valuation.isEquiv_iff_valuationSubring` and
`ValuationSubring.valuationSubring_valuation`.

The source rows M249.007 (`localSeparableValuationSubring_pullback`) and
M249.008 (the instance `localSeparableValuationHasExtension`) belong to
Task 5800, and their proofs are not in the Library at base commit
`c40a01345b2f4172fa41e07ff31644b40e695003`. This proof therefore derives
both as local hypotheses (`have hpullback` and an anonymous local `have`).
It publishes no declaration under their adapted names, and adds no
global instance.

## Source correspondence and adaptation

The source is the theorem
`LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension`,
lines 115–159 of the pinned source file (docstring lines 115–117, signature
lines 118–121, proof lines 121–159). The local pullback follows the source
proofs of M249.004 (lines 66–76) and M249.007 (lines 94–104). The local
extension instance follows M249.008 (lines 106–113).

Steps 3 and 5 are the source's: the same intermediate field `E`, the same
finite-dimensionality and separability terms, the same restrictions `Ares`
and `Bres` with their `restrictIntermediateField_hasExtension` instances,
and the same final `change zE ∈ Ares ↔ zE ∈ Bres; rw [hAB]`.

Step 4 differs from the source. The source obtains a target complete
discrete valuation on `E` from `exists_integralClosure_standard_fundamental_identity`
(M245.018) and `valuationSubring_isScalarTower_of_hasExtension`. It then
shows `target.valuation.valuationSubring = Ares` and `= Bres` with
`target_valuationSubring_eq_of_finite_separable`. The second lemma is not in
the Library. Here the published `chosenLocalExtension_uniqueValuationExtension`
(the closed specialization of M248.011 to the named chosen valuation on a
finite separable extension of a local field) plays the role of both
lemmas: it shows that each restricted valuation is equivalent to one
common valuation on `E`. Mathlib's comparison of equivalent valuations
through their valuation subrings then gives `Ares = Bres`. The mathematical
content is the same Henselian uniqueness on the finite separable field `E`.

Other adaptations: the closed target's binders are introduced with
`intro`; the namespace is prefixed with `Langlands.NYLL`; library names
are qualified; `restrictIntermediateField` is applied as a function rather
than with dot notation, because its namespace is
`Langlands.NYLL.RamificationTheory.ValuationSubring`; and the source imports
are replaced by the published Library modules listed above. Worker 85
checked this route against the exact target (diagnostic `ae5b166f`) and
described it in the task context. Worker 370 wrote and checked this
implementation.

## Original source and license

Naganori Yamaguchi (assisted by OpenAI Codex), *ClassFieldTheory (NYLL)*,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`, lines 115–159](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L115-L159).
The retained copy has SHA-256
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`. Its
lines 1–174 were read, which include the context of these theorems (the
header, namespace, `open` lines, section variables and lines 45–113). The
registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records the modifications by Worker 370 on 14 November 2026. The
existing [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This is a valuation-ring support result. It asserts nothing about host
reciprocity or class formations.
