# Galois stability of the chosen valuation ring of the separable closure: proof of M249.010

The theorem
`Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top`
has exactly the closed published type
`Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_topStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U009.Statements`).
It has no universe parameters and no further arguments.

For every nonarchimedean local field `K : Type` (with its `Field`,
`ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField`
instances), it proves
`decompositionGroup K (localSeparableValuationSubring K) = ⊤`. Here
`decompositionGroup K A` is the published abbreviation for Mathlib's
`A.decompositionSubgroup K`, the stabilizer of `A` under the pointwise
action of `SeparableClosure K ≃ₐ[K] SeparableClosure K`. So every
`K`-algebra automorphism of `SeparableClosure K` maps the chosen valuation
ring onto itself. The statement and every module it imports are unchanged.

## The implemented proof

1. **Every automorphism stabilizes the ring.** After introducing `K` and
   its instances from the closed target, `top_unique` reduces the goal to
   showing that every `sigma` lies in the decomposition group. Membership
   is, by definition, `sigma • localSeparableValuationSubring K =
   localSeparableValuationSubring K`; a `change` states this.
2. **The translate still extends the base valuation.** The published
   `smul_hasExtension` (M233.010), applied to `(localCompleteDVF K).valuation`,
   the chosen ring and `sigma`, gives a local instance
   `(localCompleteDVF K).valuation.HasExtension
   (sigma • localSeparableValuationSubring K).valuation`. Its hypothesis
   that the valuation of the chosen ring extends the base valuation is found
   by instance search: it is the published global instance
   `localSeparableValuationHasExtension` (M249.008), imported from its proof
   module.
3. **Conclusion.** The published M249.009 proof
   `localSeparableValuationSubring_eq_of_hasExtension`, applied to `K` and
   the translate, gives `localSeparableValuationSubring K =
   sigma • localSeparableValuationSubring K`; its symmetric form closes the
   goal.

The development check in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
reports 0 errors and 0 warnings. The theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Dependencies

| Role | Declaration | Module |
| --- | --- | --- |
| target | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_topStatement` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U009.Statements` |
| M249.009 proof | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U009.Proofs` |
| M249.008 instance | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationHasExtension` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U008.Proofs` |
| M233.010 | `Langlands.NYLL.RamificationTheory.ValuationSubring.smul_hasExtension` | `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.U010.Proofs` |
| M239.001 (through the statement module) | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions` |
| M249.006 (through the statement module) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` | `...LocalReciprocity.LocalResidueDatum.U006.Definitions` |

The direct imports are the M249.008 proof module, the M249.009 proof module
and the M233.010 proof module. The Mathlib declarations used are
`top_unique`, the pointwise action of
`SeparableClosure K ≃ₐ[K] SeparableClosure K` on valuation subrings (scope
`Pointwise`) and `ValuationSubring.decompositionSubgroup`. This module
declares only the theorem above; it adds no instance.

## Source correspondence and adaptation

The source is the theorem
`LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top`, lines
161–174 of the pinned source file (docstring lines 161–162, signature lines
163–164, proof lines 164–174). The proof is the source proof: the same
`top_unique`, the same `change sigma • _ = _`, the same local
`smul_hasExtension` instance and the same symmetric application of M249.009.
In the source, the `HasExtension` instance for the chosen ring is the global
instance M249.008 (lines 106–113); here it is the published proof of that
instance, which is registered as a global instance in the same way.

Other adaptations: the closed target's binders are introduced with
`intro`; the namespace is prefixed with `Langlands.NYLL`; library names are
qualified; `open scoped Pointwise` and the `decompositionGroup` namespace
are opened as in the source; and the source imports are replaced by the
published Library modules listed above. Worker 85 checked this route
against the exact target (diagnostic `ae5b166f`) and described it in the
task context. Worker 370 wrote and checked this implementation.

## Original source and license

Naganori Yamaguchi (assisted by OpenAI Codex), *ClassFieldTheory (NYLL)*,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`, lines 161–174](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L161-L174).
The retained copy has SHA-256
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`. Its
lines 1–174 were read, which include the context of this theorem (the
header, namespace, `open` lines, section variables and lines 45–159). The
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
