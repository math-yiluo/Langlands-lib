# The local decomposition residue field is finite: proof and instance

This module proves the published closed target
`Langlands.NYLL.LocalClassFieldTheory.localDecompositionResidueFiniteStatement`
([target](Statements.md), NYLL source unit M249.014) by the theorem

```lean
theorem localDecompositionResidueFinite :
    localDecompositionResidueFiniteStatement
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, under the adapted source
name. The target is a reducible `abbrev`, so the module then registers the
theorem as a global instance, as the source does:

```lean
attribute [instance] localDecompositionResidueFinite
```

The theorem's type is the target, and neither has a level parameter. For a
nonarchimedean local field `K : Type`, let `B` be the chosen valuation ring
`localSeparableValuationSubring K` of `SeparableClosure K`. The theorem says
that `decompositionResidueField K B` is finite (Mathlib's class `Finite`).
That type is the residue field `κ` of the fixed ring of the decomposition
group of `B`. Any module that imports this one finds the `Finite` instance by
instance search.

The statement module also states the M249.016 target
`localSelectedResidueIsAlgClosedStatement`. This module does not prove it.

## Proof

The proof is the source body (lines 256–260), unchanged, after
`intro K _ _ _ _`. That intro introduces `K` and its four instance binders,
which are the source section variables. The proof has two steps.

1. **The residue field of `K` is finite.** The `have` states
   `Finite (localCompleteDVF K).residueField`. Here
   `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K` is the canonical
   valuation of `K`, packaged as a complete discrete valuation field
   ([definition](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/Canonical.md)).
   Its `residueField` is a chain of reducible abbreviations
   ([projections](../../../../../../ValuedFieldTheory/Valuation/DiscreteValuationField/Complete/Projections.md)).
   The chain ends in `IsLocalRing.ResidueField` of the valuation subring of
   that valuation. The tactic `change Finite 𝓀[K]` restates the goal with
   Mathlib's scoped `ValuativeRel` notation `𝓀[K]`, which is
   `IsLocalRing.ResidueField 𝒪[K]`. Lean accepts the two types as
   definitionally equal. `infer_instance` then closes the goal with Mathlib's
   instance `Finite 𝓀[K]` for nonarchimedean local fields, in
   `Mathlib/NumberTheory/LocalField/Basic.lean`.
2. **Transport along the residue equivalence.**
   `Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue K`
   (M249.012, [definition](../U011/Definitions.md)) is a ring isomorphism
   `(localCompleteDVF K).residueField ≃+* decompositionResidueField K B`.
   `Finite.of_equiv` applied to its underlying equivalence `.toEquiv`
   transfers finiteness to `decompositionResidueField K B`.

The proof uses no other lemma.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), on a workspace
based on Library commit `2b8ae82e90fb648bafb921c71a17200990d467af`, compiled
the module with no errors or warnings (diagnostic
`ea3ded5f-1479-4967-95ea-ada408e314c4`). Inspection of the theorem reported
kind `theorem`, no level parameters, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

A private client module that imports this one checked the instance
registration (diagnostic `8d9c235d-1ca8-4677-a7ab-a874079ae154`, no errors or
warnings). In it, `inferInstance` proves
`Finite (decompositionResidueField K (localSeparableValuationSubring K))`, and
`Fintype.ofFinite _` elaborates at type
`Fintype (decompositionResidueField K (localSeparableValuationSubring K))`.
That type is the source body of the next source instance, M249.015
`localDecompositionResidueFintype`.

## Imports and opens

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U014.Statements`
  is the published target. It supplies `localSeparableValuationSubring` and
  `decompositionResidueField`.
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U011.Definitions`
  supplies `localBaseResidueEquivDecompositionResidue` and, through its
  imports, `localCompleteDVF`, the `CompleteDVF` projections and Mathlib's
  `Mathlib.NumberTheory.LocalField.Basic`.

The opens are `Langlands.NYLL.LocalFieldTheory` (for `localCompleteDVF`),
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring` (for
`decompositionResidueField`) and `open scoped ValuativeRel` (for `𝓀[K]`). The
published target and definitions are used by name, and none of them is
modified.

## Source correspondence and changes

The original declaration is the instance
`LocalClassFieldTheory.localDecompositionResidueFinite` at lines 252–260 of
Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L252-L260)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`). It is
declared `noncomputable instance`. Its type is the published target, and its
body is the two-step proof above. The source module opens namespace
`LocalClassFieldTheory` (line 31), has `open ClassFormation` (line 33),
`open ValuationTheory RamificationTheory LocalFieldTheory` (line 35),
`noncomputable section` (line 39), `open scoped Pointwise ValuativeRel`
(line 41), `open HilbertRamification.ValuationSubring` (line 42) and
`open Field.absoluteGaloisGroup` (line 43), and declares the section
variables at lines 45–46.

Worker 370 made these changes on 15 November 2026:

- the `noncomputable instance` becomes the theorem
  `localDecompositionResidueFinite` of the closed target, followed by
  `attribute [instance]` for it. The file keeps the source's
  `noncomputable section`. The proof begins
  with `intro` of the section variables. The tactic body is otherwise the
  source's, character for character;
- the namespace is prefixed with `Langlands.NYLL`, and so are the two opened
  namespaces the proof uses. Only those two opens and `open scoped
  ValuativeRel` are kept; the other source opens are omitted;
- the source imports are replaced by the two published modules above;
- the doc comment is the source's.

No draft from another worker was used. Worker 85's development replay of the
same script against this target is described in the task context; this module
was written and checked independently.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library.
