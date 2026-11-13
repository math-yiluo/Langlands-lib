# Pulling the chosen separable valuation ring back along an embedding: target

This module states NYLL source unit M265.012 as a closed proposition. It
exports one Prop-valued definition,
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_comap_embeddingStatement`.
Nothing is proved here. The proof is a separate unit under the adapted source
name `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_comap_embedding`.

Mathematically, the target says the following. Let `K` be a nonarchimedean
local field and `L/K` a finite separable extension. Suppose `L` carries a
valuation that extends the valuation of `K`, and let `i : L → SeparableClosure K`
be a `K`-embedding. Then the preimage under `i` of the chosen valuation ring of
`SeparableClosure K` is the valuation ring of `L`. In other words, the place of
`SeparableClosure K` fixed once and for all restricts, along every
`K`-embedding, to the given place of `L`.

## The proposition

```lean
def localSeparableValuationSubring_comap_embeddingStatement : Prop :=
  ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [Algebra K L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (i : L →ₐ[K] SeparableClosure K) [Algebra.IsSeparable K L],
    (localSeparableValuationSubring K).comap i.toRingHom =
      (ValuativeRel.valuation L).valuationSubring
```

There is no level parameter: `K` and `L` live in `Type`, as in the source. The
binders, in order, are the source section variables that the source theorem
uses (lines 129–136 and 152), followed by the theorem's own instance argument
(line 164):

| Binder | Meaning |
| --- | --- |
| `K L : Type` | the base field and the extension field |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| `[Field L] [ValuativeRel L]` | `L` is a field with a valuative relation; no topology or local-field structure on `L` is assumed |
| `[Algebra K L] [FiniteDimensional K L]` | `L` is a finite extension of `K` |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | the valuation of `L` extends the valuation of `K` |
| `i : L →ₐ[K] SeparableClosure K` | a `K`-algebra embedding of `L` into the separable closure |
| `[Algebra.IsSeparable K L]` | `L/K` is separable |

On the left, `i.toRingHom` is the underlying ring map of the embedding, and
Mathlib's `ValuationSubring.comap` takes the preimage of the chosen valuation
subring of `SeparableClosure K`. The result is a valuation subring of `L`. On
the right, Mathlib's `Valuation.valuationSubring` is the valuation subring of
the valuation of `L`.

### Published declaration used

- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring K`
  (M249.006, [definition](../LocalResidueDatum/U006/Definitions.md)): the
  preimage, under the inclusion `SeparableClosure K → AlgebraicClosure K`, of a
  valuation subring of `AlgebraicClosure K` chosen by Chevalley's extension
  theorem.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the declaration reported kind
`definition`, no level parameters, `statement_returns_prop: true`, and only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

The binder list was also checked against the source in a private probe (not
part of this contribution). The probe declared the source's section variables
(lines 129–136 and 152) and its `omit` clause (lines 154–155). Under them, a
theorem with the source header (lines 163–166) took this proposition as a
hypothesis `h` and was proved by `h K L i`. It compiled with no errors or
warnings, so Lean's unused-section-variable linter found no included variable
that the closed statement leaves unused.

## Imports and scope

The only import is the published module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`.
It supplies `localSeparableValuationSubring` and, through its imports,
Mathlib's `IsNonarchimedeanLocalField`, `SeparableClosure`,
`Valuation.HasExtension`, `ValuationSubring.comap` and
`Valuation.valuationSubring`.

Only M265.012 is stated. The source section also declares
`[TopologicalSpace L]`, `[IsNonarchimedeanLocalField L]`, `[IsGalois K L]` and
the unramifiedness class `IsUnramifiedValuedExtension K L`. The source theorem
omits all four (lines 154–155), and so does this statement. The statement
also does not use the two instances declared just before the theorem
(M265.010 `comparisonIntegerRingIsIntegralClosure` and M265.011
`finiteGaloisLocalField_integerRing_moduleFinite`, lines 138–147), so they are
not ported here.

The source proof (lines 167–200) uses M249.007
`localSeparableValuationSubring_pullback` and three valuation-theory lemmas:
`hasExtension_valuation_of_valuationSubring_pullback`,
`exists_integralClosure_standard_fundamental_identity` and
`target_valuationSubring_eq_of_finite_separable`. These belong to the separate
proof unit; this module does not import them.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean#L154-L200)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `48110dffb73b0584773bf23cb7cde4ebbb32c51804442311758ebfcc934460b2`, the
value recorded for M265 in the
[public declaration partition](../../../../../../../notes/reuse/nyll-public-port/m263-m269.md#m265).

| Partition unit | Original theorem in `LocalClassFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M265.012 | `localSeparableValuationSubring_comap_embedding` | 154–200 | `localSeparableValuationSubring_comap_embeddingStatement` |

Lines 154–160 hold the `omit … in` clause and two local `open … in` clauses
for the proof's lemmas. Lines 161–162 are the doc comment. Line 163 is the
theorem name, line 164 the argument `[Algebra.IsSeparable K L]`, lines 165–166
the conclusion and lines 167–200 the source proof. The source module works in
`noncomputable section` (line 23), opens namespace `LocalClassFieldTheory`
(line 25) and opens `ValuativeRel` (scoped) and several other namespaces
(lines 27–30). The section starting at line 127 declares the variables at
lines 129–136, 149–150 and 152.

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` prefix to the namespace. The chosen ring is the
  published prefixed definition of the same name;
- packaged the theorem type as the closed proposition above. The section
  variables that the theorem uses become the leading `∀`-binders, in source
  order, with the same kinds (explicit for `K`, `L` and `i`,
  instance-implicit for the rest). The theorem's own argument
  `[Algebra.IsSeparable K L]` follows;
- left out the source variables that the source theorem omits;
- omitted the source proof and the source's `open` lines. The statement needs
  neither, because it spells out `ValuativeRel.valuation` in full;
- replaced the source imports by the published module above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `UnramifiedComparison.lean`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
