# Comparison of chosen and supplied local valuations: statement

This module defines the closed proposition
`Langlands.NYLL.LocalFieldTheory.ChosenLocalExtensionSuppliedComparisonStatement`
in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenSuppliedComparisonStatement`.
It publishes a target for a separate proof. The declaration has type `Prop`,
with no free mathematical parameters or universe parameters.

## Full telescope and conclusion

Every binder in the following definition belongs inside the proposition:

```lean
def ChosenLocalExtensionSuppliedComparisonStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [_root_.Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)],
    (chosenLocalExtensionCompleteDVF K L).valuation.IsEquiv
        (localCompleteDVF L).valuation ∧
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring =
        (localCompleteDVF L).valuation.valuationSubring
```

Both carriers are in `Type 0`, as required by the published
`chosenLocalExtensionCompleteDVF`. The proposition quantifies over supplied
field structures and a supplied finite-dimensional separable `Algebra K L`.
Each field has its own supplied `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` structure. In particular the local-field
structure on `L` is independently supplied; it is not replaced by a structure
constructed from the chosen valuation.

The raw hypothesis is Mathlib's
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`.
For the supplied `Algebra K L`, this class asserts
`(ValuativeRel.valuation K).IsEquiv
  ((ValuativeRel.valuation L).comap (algebraMap K L))`.
Thus compatibility is along the actual supplied `algebraMap K L`. There is
no replacement field embedding or extra equation for this map.

The left valuation in both conjuncts is exactly
`(chosenLocalExtensionCompleteDVF K L).valuation`. It depends on the
supplied algebra and base local-field structure. The right valuation is
exactly `(localCompleteDVF L).valuation`, the canonical complete-DVF package
of the independently supplied upstairs structure. This projection is
definitionally `ValuativeRel.valuation L`.

Mathlib's `Valuation.IsEquiv v₁ v₂` means
`∀ x y, v₁ x ≤ v₁ y ↔ v₂ x ≤ v₂ y`: the valuations induce the same
preorder on `L`, allowing different value groups and normalizations.
The chosen valuation is the first argument, and the supplied valuation is
the second. The second conjunct is equality in `ValuationSubring L` of
the two actual subrings inside this same `L`. For every `x : L`, their
membership predicates are respectively the chosen and supplied inequalities
`v x ≤ 1`. No abstract ring equivalence or transport to another field is
substituted for this equality. Mathlib's
`Valuation.isEquiv_iff_valuationSubring` relates these two conclusions.

The identity extension is included: take `L = K`, the identity algebra,
and the same supplied local structures; Mathlib supplies finite
dimensionality, separability and reflexive valuation extension. There is no
proper-extension condition. No uniqueness, integral-closure, finite-module,
completeness, topology-comparison or conclusion certificate is added as a
hypothesis.

## Derived provenance and imports

This is an internal supplied-data specialization of published adaptations
of Naganori Yamaguchi's NYLL results. It is not a literal declaration in
the original source,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete 206-line source was read; its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
The source-to-derived correspondence is:

| Published declaration | Original unit | Role in the derived target |
| --- | --- | --- |
| `localCompleteDVF` | M248.001, lines 34–55 | Packages the supplied valuation on each local field. |
| `localCompleteDVFValuation_hasExtension` | M248.002, lines 58–74 | Converts the raw compatibility hypothesis to compatibility of the canonical packages. |
| `chosenLocalExtensionCompleteDVF` | M248.006, lines 130–138 | Supplies the exact chosen valuation compared here. |
| `chosenLocalExtension_uniqueValuationExtension` | Adaptation of M248.011, lines 194–204 | Compares that chosen valuation with every extension of the canonical base valuation. |

The published uniqueness theorem has the closed target
`ChosenLocalExtensionUniqueValuationExtensionStatement.{y}` with arbitrary
comparison value-group universe `y`. Specializing the comparison valuation
to `(localCompleteDVF L).valuation`, after using canonical extension
compatibility, motivates the first conjunct here. The valuation-subring
criterion motivates the second. This describes the provenance of the
target; this module does not implement that proof.

The only direct imports are `Mathlib.RingTheory.Valuation.Extension` and
the published sibling `Chosen` module. The latter transitively imports
`Canonical`. They supply all data and predicates used in the definition.
The extension and uniqueness proofs are described above for provenance;
they need not be imported to state this proposition.

The published canonical and chosen definitions, their dependencies, and
existing instances are preserved. The module adds only this Prop-valued
definition. Its proof, host inertia, finite reciprocity, cohomological
agreement and Weil-system statements are separate work.

## Development check

The entry module compiles in the approved Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment with no errors or
warnings. Inspection of the exact unapplied declaration reports a
definition returning `Prop` with no universe parameters. Its dependencies
use only `propext`, `Classical.choice` and `Quot.sound`. These are
development checks; independent semantic review and publication are
separate steps.

## Attribution and adaptation

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No source-specific errata file was found in the workspace, project notes
or current Library.

The original copyright and author header is retained verbatim.
The inherited [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are preserved. Published
canonical and chosen adaptations are by Worker 785; the published chosen
uniqueness statement and proof are by Worker 1199, with Worker 106 credited
for that statement's formulation.

On 1 November 2026, Worker 106 supplied this target's exact telescope and
the supplied-data comparison rationale. Worker 1199 implemented the closed
definition, documented its conventions and derived provenance, and wrote
this explanation. These are the actual formulation and adaptation
coauthors of this unit. No original proof text is copied.
