# The fixed field of an abstract compositum: proposition target

This module defines one Prop-valued definition in
`namespace Langlands.NYLL.LocalClassFieldTheory`, with `open ClassFormation`:

```lean
def finiteAbelianSubextension_compositum_fixedFieldStatement
    (K : Type) [Field K]
    (U T : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  abstractFixedField K (SeparableClosure K) (U.compositum T).field =
    abstractFixedField K (SeparableClosure K) U.field ⊔
      abstractFixedField K (SeparableClosure K) T.field
```

## Meaning

Let `K` be a field in `Type` (universe zero), let `Ω = SeparableClosure K` be
Mathlib's chosen separable closure and let `G_K = Gal(Ω/K)`, which is
`intrinsicAbsoluteGalois K`. The closed subgroup `intrinsicAbstractBase K` is
the fixing subgroup of the bottom intermediate field `⊥ : IntermediateField K Ω`.
Arguments `U T : FiniteAbelianSubextension (intrinsicAbstractBase K)` are
finite abelian subextension packages over that subgroup (the published M296
structure): each carries a closed subgroup `.field` of `G_K`, contained in
`intrinsicAbstractBase K` and normal in it with finite commutative quotient.

`U.compositum T` is the published M296.017 compositum package, whose
subgroup `(U.compositum T).field` is the intersection of `U.field` and
`T.field` (the source docstring: "contravariantly represented by
`G_{L₁} ∩ G_{L₂}`"). For a closed subgroup `H`, `abstractFixedField K Ω H` is
the intermediate field `IntermediateField.fixedField H.toSubgroup` of `Ω / K`.

The target says that the fixed field of the compositum subgroup equals the
supremum, in the lattice `IntermediateField K Ω`, of the two fixed fields
`abstractFixedField K Ω U.field` and `abstractFixedField K Ω T.field`, i.e. the
smallest intermediate field of `Ω / K` containing both (their compositum in
`Ω`). The equality is between intermediate fields of the same extension
`Ω / K`. No valuation, topology, local-field or finite-dimensionality
hypothesis is placed on `K`. This is a proposition definition; no proof is
asserted.

## Source

The original is Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean#L126-L132),
lines 126–132 (docstring 126–127, type 128–132; the proof, lines 133–144, is
omitted). The whole source file was read; its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.

| Unit | Source declaration | Adapted declaration |
| --- | --- | --- |
| M300.005 | theorem `LocalClassFieldTheory.finiteAbelianSubextension_compositum_fixedField` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_compositum_fixedFieldStatement` |

The source context, lines 25–32, is `noncomputable section`,
`namespace LocalClassFieldTheory`,
`open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory`,
`open ClassFormation` and `variable (K : Type) [Field K]`; the file declares no
`universe`. The source theorem mentions `K`, so its complete telescope is
`(K : Type) [Field K] (U T : FiniteAbelianSubextension (intrinsicAbstractBase K))`,
with `K`, `U` and `T` explicit.

Every source name used in the type resolves to a published Library
declaration with the same body, which is reused by Lean name:

| Source declaration | Published declaration (unit) | Module |
| --- | --- | --- |
| `ClassFormation.FiniteAbelianSubextension`, `.field` | `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension`, `.field` (M296.001–.002) | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions` |
| `ClassFormation.FiniteAbelianSubextension.compositum` | `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.compositum` (M296.017) | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Compositum` |
| `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (M091.003) | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions` |
| `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` (M099.001) | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |
| `SeparableClosure`, `⊔` on `IntermediateField` | the same Mathlib declarations | — |

As recorded with M099.001, `abstractFixedField` does not use its section's
`[IsGalois k Ω]` variable, so no Galois instance on `SeparableClosure K` enters
this target.

This is unit M300.005 of the published
[NYLL port partition](../../../../../../../../notes/reuse/nyll-public-port-plan.md)
(appendix row in `notes/reuse/nyll-public-port/m289-m312.md`, section M300).

## Modifications

Worker 451 made these modifications, and no others:

- The source theorem's type is extracted and closed over its complete
  telescope as a `def ... : Prop`; the name is prefixed with `Langlands.NYLL`
  and receives the suffix `Statement`. The section variables
  `(K : Type) [Field K]` become explicit leading binders, in the source order
  and with the source binder kinds.
- The source proof (lines 133–144) is omitted; it remains a separate proof
  obligation.
- The source imports (`Existence.LocalAbsoluteData`,
  `LocalReciprocity.IntrinsicAbsoluteData`, `LocalReciprocity.SeparableUnitsNorm`,
  `LocalReciprocity.TopologicalReciprocity` and
  `Mathlib.FieldTheory.Galois.Abelian`) are replaced by the published modules
  `Reciprocity.FiniteAbelianSubextension.Compositum`,
  `IntrinsicAbsoluteData.Initial.Definitions` and
  `FiniteAbstractFixedField.Initial.Definitions`, which supply every
  declaration used. The successful focused check below confirms that this
  import set suffices; the target needs neither M300.001–.004, the norm
  subgroup M300.003, nor the source proof ingredients.
- The unused openings `LocalFieldTheory`, `RamificationTheory`,
  `CyclicCohomology` and `KummerTheory` are dropped; `ClassFormation` is kept.
- The docstring is the source docstring unchanged.

No local, scoped or global instance is introduced, and no other worker's
draft was reused.

The source was read from the retained snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No NYLL erratum is recorded in the Library's errata notes.

The original copyright and author header is retained. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) in the Library are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development checks

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), check
`0dc8f8b3-4238-4aeb-a296-0ee45a99ed78` compiled this module with no errors or
warnings and inspected the declaration as a definition with
`statement_returns_prop: true` and no universe parameters. A private
diagnostic, check `da37ffa4-5db6-442d-a484-8fa751218b3e`, printed the
telescope
`(K : Type) → [Field K] → FiniteAbelianSubextension (intrinsicAbstractBase K) → FiniteAbelianSubextension (intrinsicAbstractBase K) → Prop`
and confirmed by `rfl` three facts written with fully qualified names: the
declaration equals the displayed body (with
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.compositum`,
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` and
`Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase`);
`(U.compositum T).field` is `U.field ⊓ T.field`; and
`abstractFixedField K (SeparableClosure K) H` is
`IntermediateField.fixedField H.toSubgroup`. The diagnostic is not part of this
contribution. Independent semantic acceptance and the proof are separate
obligations.
