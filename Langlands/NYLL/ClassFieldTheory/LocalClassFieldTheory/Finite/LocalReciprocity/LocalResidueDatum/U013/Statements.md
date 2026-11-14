# Naturality of the base-residue comparison: target

This module states NYLL source unit M249.013 as a closed proposition. It
exports one Prop-valued `def` in namespace
`Langlands.NYLL.LocalClassFieldTheory`:

- `localBaseResidueEquivDecompositionResidue_algebraMapStatement` (M249.013).

Nothing is proved here. The proof is a separate unit under the adapted source
name `Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue_algebraMap`.

Mathematically, let `K` be a nonarchimedean local field and let `𝒪` be the
valuation ring of the canonical complete discrete valuation of `K`, with
residue field `k = 𝒪/𝔪`. Let `B` be the valuation ring
`localSeparableValuationSubring K` of the separable closure `K^sep` chosen in
M249.006, let `Z` be its decomposition group over `K`, let `κ` be the residue
field of the fixed subring `B^Z`, and let `λ = B/𝔪_B` be the residue field of
`B`. The comparison `φ : k ≃+* κ` of M249.012 and the inclusion `κ → λ` of
residue fields fit into a commutative square with the literal reduction map.
For every `x ∈ 𝒪`:

```
(κ → λ) (φ (x mod 𝔪)) = (x viewed in B) mod 𝔪_B.
```

The source docstring calls this the naturality of the base-residue comparison
with the literal reduction map into the selected residue field.

## The proposition

```lean
def localBaseResidueEquivDecompositionResidue_algebraMapStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : (localCompleteDVF K).valuationSubring),
    algebraMap
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (localBaseResidueEquivDecompositionResidue K
          (IsLocalRing.residue (localCompleteDVF K).valuationSubring x)) =
      IsLocalRing.residue (localSeparableValuationSubring K)
        (⟨algebraMap K (SeparableClosure K) (x : K),
          (localSeparableValuationSubring_pullback K (x : K)).2
            x.property⟩ : localSeparableValuationSubring K)
```

There is no level parameter: `K` lives in `Type`, as in the source. The
quantified binders, in order, are the section variables of the source (lines
45–46) followed by the theorem's own explicit binder `x`.

| Binder | Meaning |
| --- | --- |
| `K : Type` | the base field |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| `x : (localCompleteDVF K).valuationSubring` | an element of the valuation ring `𝒪` of the canonical complete discrete valuation of `K` |

The left-hand side reduces `x` modulo the maximal ideal of `𝒪`
(`IsLocalRing.residue`), applies the comparison `φ`, and then the algebra map
`κ → λ`. The right-hand side is the residue modulo the maximal ideal of `B`
of the image `algebraMap K (SeparableClosure K) x`. That image lies in `B`
by the backward direction of M249.007 applied to the membership proof
`x.property`; this proof term only builds the subtype element and is the
source's own term.

### Published declarations used

- `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K`
  ([definition](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/Canonical.md)):
  the canonical complete discrete valuation datum of the local field `K`. Its
  projections `valuationSubring` and `residueField`
  ([definitions](../../../../../../ValuedFieldTheory/Valuation/DiscreteValuationField/Complete/Projections.md))
  are the valuation ring `𝒪` as a type and its residue field
  `IsLocalRing.ResidueField 𝒪`.
- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring K`
  (M249.006, [definition](../U006/Definitions.md)): the valuation ring `B` of
  `SeparableClosure K`, the preimage of a valuation subring of
  `AlgebraicClosure K` chosen by Chevalley's extension theorem.
- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_pullback`
  (M249.007, [target](../U007/Statements.md) and [proof](../U007/Proofs.md)):
  for `y : K`, `algebraMap K (SeparableClosure K) y ∈ B` if and only if
  `y ∈ 𝒪`.
- `Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue K`
  (M249.012, [definition](../U011/Definitions.md)): the ring isomorphism
  `φ : k ≃+* κ`. It is the residue map of the isomorphism of `𝒪` with the
  valuation ring of the decomposition field (M249.011), followed by
  `decompositionFieldResidueEquiv` (M243.018).
- `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField`
  (M243.003) and `...selectedResidueField` (M243.004),
  [definitions](../../../../../../ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence/Definitions.md):
  `κ` is the quotient of `B^Z` by the contraction of the maximal ideal of `B`,
  and `λ` is `IsLocalRing.ResidueField B`.
- `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra`
  (M243.021) and `decompositionResidueField.instField` (M243.020),
  [instances](../../../../../../ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence/ResidueFields.md):
  the field structure on `κ` and the algebra `κ → λ`, given by
  `Ideal.Quotient.algebraQuotientOfLEComap`. It sends the class of
  `z ∈ B^Z` to the residue of `z` in `λ`. The `algebraMap` in the statement
  is this instance.

The Galois instance `IsGalois K (SeparableClosure K)` used by
`decompositionResidueField` and by the algebra instance is Mathlib's. The
statement needs neither of the local instances M249.001 and M249.002.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), against Library
commit `88a89ad3bebce4b6ac7149eccc33c571d805fba5`, compiled the module with no
errors or warnings (diagnostic `4682259c-e7f3-49eb-b5ef-8f452ce95f08`).
Inspection reported kind `definition`, no level parameters,
`statement_returns_prop: true`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

A private probe compiled against this module (diagnostic
`b21e7595-6b54-45b5-b43f-de380fc5fb63`, no errors or warnings) proved the
target by `intro K _ _ _ _ x; rfl`, the source proof after introducing the
binders. This is a check that the target is the intended definitional
identity; the proof is not part of this module.

## Imports and scope

The imports are the published modules
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U011.Definitions`
(for `localBaseResidueEquivDecompositionResidue`, and through its imports
`localCompleteDVF` with its projections, `localSeparableValuationSubring`,
`localSeparableValuationSubring_pullback`, `decompositionResidueField` and
`selectedResidueField`) and
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`
(for the instances M243.020 and M243.021).

Only M249.013 is stated. The neighbouring source units M249.014 and M249.016
are stated in the [U014 target module](../U014/Statements.md); M249.015 is a
`Fintype` instance (data) left for a definition unit.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L235-L250)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`, the
value recorded for M249 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m249).

| Partition unit | Original declaration in `LocalClassFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M249.013 | theorem `localBaseResidueEquivDecompositionResidue_algebraMap` | 235–249 (proof 249–250) | `localBaseResidueEquivDecompositionResidue_algebraMapStatement` |

Lines 235–238 are the doc comment, line 239 the theorem name, and lines
240–249 its binder and type; the proof is `by rfl` (lines 249–250). The source
module opens namespace `LocalClassFieldTheory` (line 31), opens
`RamificationTheory` and `LocalFieldTheory` (line 35) and
`HilbertRamification.ValuationSubring` (line 42), works in
`noncomputable section` (line 39) and declares the section variables at lines
45–46.

Worker 85 made these changes on 14 November 2026:

- added the `Langlands.NYLL` prefix to the namespace and to the opened
  namespaces, which become `Langlands.NYLL.LocalFieldTheory` and
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`;
- packaged the theorem type as a closed proposition, a `def` with the suffix
  `Statement`. The section variables become the leading `∀`-binders, with the
  same kinds (explicit for `K`, instance-implicit for the rest), followed by
  the explicit binder `x`. The type after the binders is the source type
  unchanged;
- omitted the proof, the `noncomputable section`, the other `open` lines and
  all other declarations;
- replaced the source imports by the published modules above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `LocalResidueDatum.lean`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
