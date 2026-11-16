# The chosen prime element is a prime element

This module proves the theorem
`Langlands.NYLL.ClassFormation.ValuationData.chosenPrimeElement_isPrime`, the proof phase of
M030.003 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m030).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.ValuationData.chosenPrimeElement_isPrimeStatement` applied to the
theorem's parameters:

```lean
theorem chosenPrimeElement_isPrime (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    chosenPrimeElement_isPrimeStatement v K
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (the universe-zero type of acting groups that Mathlib's `Rep ℤ G` requires) and `{D : DegreeData G} {A : Rep ℤ G}`, in `namespace ValuationData`. The theorem takes `v` and `K`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Statements`, the target is the proposition

```lean
v.IsPrimeElement K (v.chosenPrimeElement K)
```

Here `v : ValuationData D A` (M025.012) is a valuation datum for the degree datum `D` and the integral representation `A`, `K : FiniteAbstractField G` (M010.121) a finite abstract field, and `v.valuationAt K` (M025.025) the normalized valuation `v_K` on `A_K = ambientFixedAddSubgroup A K.field` (M023.001), with values in the value group `v.valueGroup` (M025.013). `v.oneValue` (M028.005) is the value `1` of the value group. `v.chosenPrimeElement K` (M030.001) is `Classical.choose` of the existence of an element of valuation `v.oneValue` (from the surjectivity of `v_K`, M025.027, whose source proof the published definition carries in place). `v.IsPrimeElement K π` (M028.007) is `v.valuationAt K π = v.oneValue`. The target says that the chosen element is a prime element. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice.ChosenPrime.Statements`, which defines the target and imports `chosenPrimeElement` (M030.001), `oneValue` (M028.005), `IsPrimeElement` (M028.007), `unitAddSubgroup` (M028.008) and the valuation data with `valuationAt` (M025.025).

The module opens `KummerTheory` and `CyclicCohomology` and declares the variables, as the source does.

## Implemented proof

The source proof is the term `v.valuationAt_chosenPrimeElement K`, M030.002, whose proof is not yet in the Library. The module proves M030.002 as the private theorem `valuationAt_chosenPrimeElement_aux` with its source statement. The source term is `Classical.choose_spec (v.normalizedValuation_surjective K v.oneValue)`, which names M025.027 `normalizedValuation_surjective`, whose proof is not yet in the Library; the published definition `chosenPrimeElement` contains the source proof of M025.027 in its place. The port writes `Classical.choose_spec (p := fun a => v.valuationAt K a = v.oneValue) _`: with the predicate given explicitly, unification finds the existence proof as the argument of `Classical.choose` inside `chosenPrimeElement`, so the term proves `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`. After `show` states the published proposition unfolded, the main proof is `valuationAt_chosenPrimeElement_aux v K`, accepted because `IsPrimeElement` unfolds by definition to the equation it proves.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`, lines 39–50](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean#L39-L50):
the theorem M030.002 `valuationAt_chosenPrimeElement` with its docstring and attribute at lines 39–44, which the proof uses, and the docstring at line 46 and the theorem at lines 47–50. They lie in `namespace ClassFormation` (line 17), with `open KummerTheory` (line 19) and `open CyclicCohomology` (line 21), its `noncomputable section` (line 25) and `namespace ValuationData` (line 27) with the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and `{D : DegreeData G} {A : Rep ℤ G}` (lines 30–31). The source is:

```lean
/-- Establishes the identity `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`. -/
@[simp]
theorem valuationAt_chosenPrimeElement (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.valuationAt K (v.chosenPrimeElement K) = v.oneValue :=
  Classical.choose_spec (v.normalizedValuation_surjective K v.oneValue)

/-- The chosen prime element has valuation equal to the distinguished degree-one value. -/
theorem chosenPrimeElement_isPrime (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.IsPrimeElement K (v.chosenPrimeElement K) :=
  v.valuationAt_chosenPrimeElement K
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean`;
its SHA-256 is `e0990f82b6186844d73a340de97bcbc03ba4a270924f91b120841189c49b924d`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `chosenPrimeElement_isPrimeStatement v K` as its type, and begin the proof with `show` stating it unfolded;
- prove M030.002 as the private theorem `valuationAt_chosenPrimeElement_aux` by `Classical.choose_spec` with the explicit predicate, as described above, and use it in place of `v.valuationAt_chosenPrimeElement K`;
- omit all other source declarations.

The theorem's name, docstring and binders are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M030.003. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
