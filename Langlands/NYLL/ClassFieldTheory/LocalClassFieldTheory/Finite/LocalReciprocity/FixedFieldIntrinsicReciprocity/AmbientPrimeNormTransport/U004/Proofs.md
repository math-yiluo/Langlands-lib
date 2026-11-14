# The image of the chosen transported unit has valuation one: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_targetStatement`
(NYLL source unit M283.004) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_target`.
Its only import is the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U003.Statements`.
That module imports the definition module `AmbientPrimeNormTransport.U002.Definitions`,
which in turn imports the proof module `AmbientPrimeNormTransport.U001.Proofs`
of `exists_valuationOne_unit_of_ringEquiv` (source unit M283.001). The
statement pair and everything it imports are unchanged.

## Exact target

The theorem's type is exactly
`chosenValuationOneUnitOfRingEquiv_targetStatement`. Unfolded, it says:

```lean
∀ (L M : Type)
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  (phi : L ≃+* M)
  (hmem : ∀ x : L,
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring),
  Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap M
      (Additive.ofMul
        (Units.mapEquiv phi.toMulEquiv
          (chosenValuationOneUnitOfRingEquiv L M phi hmem))) = 1
```

In words: for nonarchimedean local fields `L` and `M` and a ring
equivalence `phi` that matches their rings of integers, the image under `phi` of the chosen unit `chosenValuationOneUnitOfRingEquiv L M phi hmem : Lˣ` (source unit M283.002), the unit of `M` whose underlying element is `phi` of the chosen unit, has normalized valuation `1` in `M`.

## Proof

The definition `chosenValuationOneUnitOfRingEquiv L M phi hmem` is
`Classical.choose (exists_valuationOne_unit_of_ringEquiv L M phi hmem)`,
a witness of the existential proved by the published theorem
`Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv`.
The proof

1. introduces the twelve binders with `intro`: the fields `L` and `M`,
   eight anonymous instance binders, the equivalence `phi` and the
   hypothesis `hmem`, and
2. closes the goal with the original term: `Classical.choose_spec` applied
   to `exists_valuationOne_unit_of_ringEquiv L M phi hmem` proves the
   conjunction of the two valuation equations for the chosen witness, and
   its second component `.2` is the goal, up to unfolding the definition.

The proof has the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`
(SHA-256
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`),
theorem `chosenValuationOneUnitOfRingEquiv_target`: docstring lines 125–126, signature lines 127–140, proof lines 141–142.

Adaptation changes:

- The theorem gets the `Langlands.NYLL` namespace prefix and proves the
  published closed proposition instead of carrying the binders in its
  signature. The proof therefore starts with `intro`.
- After the `intro`, the proof term is the original term
  `(Classical.choose_spec (exists_valuationOne_unit_of_ringEquiv L M phi hmem)).2`.
- The single import replaces the original imports. The original
  `noncomputable section`, the namespace openings (unused here) and all
  other declarations of the module are omitted.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56. Worker 604 reused this shared draft on 14 November
2026, checked its source correspondence, and corrected the binder count
in the documentation; the license links were verified. The retained
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are unchanged.

No instance or simp attribute is installed. The proof uses the unchanged
source term after introducing the closed proposition’s binders.
