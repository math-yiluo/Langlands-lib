# The chosen valuation rings under a finite separable extension: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData.U006.Statements`,
source row M272.006) as the theorem

```lean
theorem localSeparableValuationSubring_eq_comap_finiteExtensionEquiv :
    localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement
```

in the namespace `Langlands.NYLL.LocalClassFieldTheory`. The statement says:
for a finite separable extension `F / K` of nonarchimedean local fields whose
valuation extends that of `K`, an embedding `i : F →ₐ[K] SeparableClosure K`
(making `SeparableClosure K` an `F`-algebra) and an `F`-algebra isomorphism
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K`, the chosen valuation ring
`localSeparableValuationSubring F` is the pullback along `e` of
`localSeparableValuationSubring K`. The same module's second proposition
(M272.007) is not proved here.

## Proof

The proof is the source proof, with the published Library names.

1. `intro K F _ _ _ _ _ _ _ _ _ _ _ _ i` introduces the two fields, their
   twelve instance hypotheses and the embedding `i`. The statement's three
   `letI` lines are inlined by Lean, so they need no `intro`. As in the
   source, the proof restates them with `let` (the `F`-algebra structure
   on `SeparableClosure K` from `i`, its separability over `F` and the
   `IsSepClosure` instance), with the same terms, and then introduces `e`.
2. With `A := localSeparableValuationSubring K` and
   `B := A.comap e.toRingHom`, the published theorem
   `localSeparableValuationSubring_comap_embedding` (M265.012), applied to
   `K`, `F` and `i`, gives `hcomap`: the pullback of `A` along `i` is the
   valuation ring of `ValuativeRel.valuation F`.
3. `hBext`: the valuation of `(localCompleteDVF F)` (M248.001) has `B`'s
   valuation as an extension. This follows from the published theorem
   `hasExtension_valuation_of_valuationSubring_pullback` (M110.004), whose
   remaining hypothesis asks, for each `x : F`, that
   `algebraMap F (SeparableClosure F) x ∈ B` exactly when `x` is in the
   valuation ring of `(localCompleteDVF F).valuation`. Unfolding `B`, the
   left side is `e (algebraMap F (SeparableClosure F) x) ∈ A`. `e.commutes`
   rewrites it to `algebraMap F (SeparableClosure K) x ∈ A`, which is
   membership of `x` in `A.comap i.toRingHom` because the algebra structure
   comes from `i`. `hcomap` turns that into membership in the valuation ring
   of `ValuativeRel.valuation F`. The `change` steps use that this ring and
   the ring of `(localCompleteDVF F).valuation` agree by unfolding the
   definitions.
4. With `hBext` as a local instance, the published theorem
   `localSeparableValuationSubring_eq_of_hasExtension` (M249.009) applied to
   `F` and `B` gives `localSeparableValuationSubring F = B`, which is the
   goal.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Library declarations used

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M272.006 statement | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement` (module `...LocalReciprocity.FixedFieldLocalData.U006.Statements`) |
| M265.012, `LocalClassFieldTheory.localSeparableValuationSubring_comap_embedding` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_comap_embedding` (module `...LocalReciprocity.UnramifiedComparison.ComapEmbeddingProof`) |
| M249.009, `LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension` (module `...LocalReciprocity.LocalResidueDatum.U009.Proofs`) |
| M110.004, `ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback` | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback` (module `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U004.Proofs`) |
| M248.001, `LocalFieldTheory.localCompleteDVF` | `Langlands.NYLL.LocalFieldTheory.localCompleteDVF` (imported through the M249.009 module) |
| M249.006, `LocalClassFieldTheory.localSeparableValuationSubring` | as in the statement module |

The four imported modules are the statement module and the modules in rows
two to four. `hasExtension_valuation_of_valuationSubring_pullback` is reached
through an `open … in` prefix naming only it, as in the source, and
`localCompleteDVF` through `open Langlands.NYLL.LocalFieldTheory`.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean>)
(SHA-256
`e629ef932276f009cee72064f4b1dffe03aa262dcd391da5a6e98c4c9008f3cd`). The
`open … in` prefix occupies lines 205–207, the M272.006 docstring lines
208–210, its signature lines 211–230 and its proof lines 231–258.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the source proof:

- The theorem proves the published closed proposition instead of restating
  the signature, so it begins with `intro` for the quantified variables.
  The tactic steps after that are the source text.
- Names are prefixed with `Langlands.NYLL`, including the namespace in the
  `open … in` prefix; the proof opens `Langlands.NYLL.LocalFieldTheory` for
  `localCompleteDVF`, as the source does with `open LocalFieldTheory`.
- The imports are the published modules listed above. The other source
  declarations and `open` lines are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0 notice,
and records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files.
