# Valuation equivalence from equal valuation subrings

This module proves the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.valuation_isEquiv_of_valuationSubring_eq`, the proof phase of
M109.007 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m109).
Its type is the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.valuation_isEquiv_of_valuationSubring_eqStatement` applied to the
theorem's parameters:

```lean
theorem valuation_isEquiv_of_valuationSubring_eq
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) :
    valuation_isEquiv_of_valuationSubring_eqStatement target v' hsub
```

## Target and binders

The section variables are those of the published statement module: `{L : Type w} [Field L]` in `namespace DiscreteValuationField.ValuedExtension` and `(target : CompleteDVF.{w, x} L)` in `section Comparison`, with `universe w x y`. The source's further variables `{K : Type u} [Field K] [Algebra K L]` and universes `u v` are omitted, as in the published statement: the theorem does not use them. The theorem takes `Gamma'` with its instance, `v'` and `hsub`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension.Statements`, the target is the proposition

```lean
target.valuation.IsEquiv v'
```

Here `target : CompleteDVF L` is a complete discretely valued field structure on the field `L` (the published `CompleteDVF`), `target.valuation` its valuation, `v'` an arbitrary valuation on `L` with values in a linearly ordered commutative group with zero `Gamma'`, and `hsub` the hypothesis that the two valuations have the same valuation subring. `Valuation.IsEquiv` is Mathlib's equivalence of valuations (they induce the same order on `L`). The target says that equal valuation subrings force equivalent valuations. The hypothesis `hsub` is a binder of the published statement that the proposition itself does not mention; the proof uses it. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension.Statements`, which defines the target and imports `CompleteDVF` through the published `Complete.Definitions` module.

The module opens no namespace, as the source.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source term: the reverse direction of Mathlib's `Valuation.isEquiv_iff_valuationSubring` (`v₁.IsEquiv v₂ ↔ v₁.valuationSubring = v₂.valuationSubring`), applied to `target.valuation`, `v'` and `hsub`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationExtension.lean`, lines 209–215](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationExtension.lean#L209-L215):
the docstring at line 209 and the theorem at lines 210–215. It lies in `namespace ValuationTheory` (line 18), its `noncomputable section` (line 20), `universe u v w x y` (line 22), `namespace DiscreteValuationField` (line 24) and `namespace ValuedExtension` (line 25) with the variables `{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]` (line 27), and `section Comparison` (line 205) with `variable (target : CompleteDVF.{w, x} L)` (line 207). The source is:

```lean
/-- Equality of valuation subrings implies valuation equivalence. -/
theorem valuation_isEquiv_of_valuationSubring_eq
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) :
    target.valuation.IsEquiv v' :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation v').2 hsub
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationExtension.lean`;
its SHA-256 is `63e3badbcec9715329fdf2a16627e8a0e7b7cbdfc9002ea69b5ada13be28e7bd`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `valuation_isEquiv_of_valuationSubring_eqStatement target v' hsub` as its type, and begin the proof with `show` stating it unfolded;
- omit the unused section variables `K`, `[Field K]`, `[Algebra K L]` and the universes `u v`, as the published statement module does;
- write the source's term proof as `exact` after the `show`;
- omit all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
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
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M109.007. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
