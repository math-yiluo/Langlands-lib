# Finite abelian subextensions over the absolute base: proposition targets

This module defines two Prop-valued definitions in
`namespace Langlands.NYLL.LocalClassFieldTheory`, with `open CyclicCohomology`
and `open ClassFormation`:

```lean
def finiteAbelianSubextension_finite_over_absoluteBaseStatement
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
    extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
      (le_baseField L.field))

def finiteAbelianSubextension_normal_over_absoluteBaseStatement
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  (extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
    (le_baseField L.field)).Normal
```

## Meaning

Let `K` be a field in `Type` (universe zero), let `Ω = SeparableClosure K` be
Mathlib's chosen separable closure and let `G_K = Gal(Ω/K)`, which is
`intrinsicAbsoluteGalois K`. The closed subgroup `intrinsicAbstractBase K` is
the fixing subgroup of the bottom intermediate field `⊥ : IntermediateField K Ω`.
An argument `L : FiniteAbelianSubextension (intrinsicAbstractBase K)` is an
actual finite abelian subextension package over that subgroup: a closed
subgroup `L.field` of `G_K` contained in `intrinsicAbstractBase K`, normal in
it with finite and commutative quotient (the published M296 structure).

The class-formation base field `baseField (intrinsicAbsoluteGalois K)` is the
closed subgroup whose underlying subgroup is `⊤`. The subgroup
`extensionSubgroup (baseField _) L.field (le_baseField L.field)` is
`L.field.toSubgroup.subgroupOf ⊤`, that is, `L.field` regarded as a subgroup of
the subgroup `⊤` of `G_K`.

- **M300.001** says that the quotient of `(baseField G_K).toSubgroup` by this
  subgroup is finite: `L.field` has finite index in the whole of `G_K`.
- **M300.002** says that this subgroup is normal: `L.field` is normal in
  the whole of `G_K`.

In both cases the hypotheses only give the corresponding property relative
to `intrinsicAbstractBase K`; the two closed subgroups `intrinsicAbstractBase K`
and `baseField G_K` are different terms, so the targets assert the transfer
from one base to the other. No valuation, topology, local-field or
finite-dimensionality hypothesis is placed on `K`. These are proposition
definitions; no proof is asserted.

The containment proof is the published theorem
`Langlands.NYLL.ClassFormation.le_baseField L.field`, whose type is the
published `le_baseFieldStatement L.field`, which unfolds to
`L.field.toSubgroup ≤ (baseField G_K).toSubgroup`. Its argument is unused by
`extensionSubgroup` (an anonymous proof binder), exactly as in the source.

## Source

The original is Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean).
The whole source file was read; its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.

| Unit | Source lines | Source declaration | Adapted declaration |
| --- | --- | --- | --- |
| M300.001 | 34–40 (docstring 34–35, type 36–40; proof 41–46 omitted) | theorem `LocalClassFieldTheory.finiteAbelianSubextension_finite_over_absoluteBase` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_finite_over_absoluteBaseStatement` |
| M300.002 | 48–53 (docstring 48–49, type 50–53; proof 54–75 omitted) | theorem `LocalClassFieldTheory.finiteAbelianSubextension_normal_over_absoluteBase` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_normal_over_absoluteBaseStatement` |

The source context, lines 25–32, is `noncomputable section`,
`namespace LocalClassFieldTheory`,
`open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory`,
`open ClassFormation` and `variable (K : Type) [Field K]`; the file declares no
`universe`. Both source theorems mention `K`, so their complete telescopes are
`(K : Type) [Field K] (L : FiniteAbelianSubextension (intrinsicAbstractBase K))`,
with `K` and `L` explicit (the source itself calls
`finiteAbelianSubextension_finite_over_absoluteBase K L` at line 95).

Every source name used in the two types resolves to a published Library
declaration with the same body, which is reused by Lean name:

| Source declaration | Published declaration (unit) | Module |
| --- | --- | --- |
| `ClassFormation.FiniteAbelianSubextension`, `.field` | `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension`, `.field` (M296.001–.002) | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions` |
| `LocalClassFieldTheory.intrinsicAbsoluteGalois`, `intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois`, `intrinsicAbstractBase` (M091.001, M091.003) | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions` |
| `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField` (M010.003) | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions` |
| `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField` (M010.005) | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` |
| `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002) | `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| `Finite`, `Subgroup.Normal`, `SeparableClosure` | the same Mathlib/core declarations | — |

These are units M300.001 and M300.002 of the published
[NYLL port partition](../../../../../../../../notes/reuse/nyll-public-port-plan.md)
(appendix row in `notes/reuse/nyll-public-port/m289-m312.md`, section M300).

## Modifications

Worker 451 made these modifications, and no others:

- Each source theorem's type is extracted and closed over its complete
  telescope as a `def ... : Prop`; the name is prefixed with `Langlands.NYLL`
  and receives the suffix `Statement`. The section variables
  `(K : Type) [Field K]` become explicit leading binders of each definition,
  in the source order and with the source binder kinds.
- The source proofs (lines 41–46 and 54–75) are omitted; they remain
  separate proof obligations.
- The source imports (`Existence.LocalAbsoluteData`,
  `LocalReciprocity.IntrinsicAbsoluteData`, `LocalReciprocity.SeparableUnitsNorm`,
  `LocalReciprocity.TopologicalReciprocity` and
  `Mathlib.FieldTheory.Galois.Abelian`) are replaced by the three published
  modules `FiniteAbelianSubextension.Definitions`, `Degree.Fields.U005.Proofs`
  and `IntrinsicAbsoluteData.Initial.Definitions`, which supply every
  declaration used. The successful focused check below confirms that this
  import set suffices; in particular the targets need neither the norm
  subgroup, the Artin map, the local-field structure nor the source proof
  ingredients (`FiniteGaloisSubextension.finite_extension_trans`,
  `closedFixingSubgroup_bot_eq_baseField`).
- The unused openings `LocalFieldTheory`, `RamificationTheory` and
  `KummerTheory` are dropped; `CyclicCohomology` and `ClassFormation` are kept.
- The docstrings are the source docstrings unchanged.

No equivalent Library or Mathlib declaration exists: a search of the Library
for these names, for `baseField (intrinsicAbsoluteGalois …)` and for
`FiniteAbelianSubextension` consumers found none, and the statements concern the
NYLL package `FiniteAbelianSubextension`, which Mathlib does not have. No local,
scoped or global instance is introduced, and no other worker's draft was
reused.

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
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), checks
`e0a2ef46-7f2c-4eab-acff-31c14e4a3c63` and
`bc579225-b03e-4373-b920-92a5b4d0932e` compiled this module with no errors or
warnings and inspected each declaration as a definition with
`statement_returns_prop: true` and no universe parameters. A private
diagnostic, check `e81dc906-609e-471d-8028-cdba7d188cb7`, printed both
declarations with full names and universes, showing the telescope
`(K : Type) → [Field.{0} K] → FiniteAbelianSubextension.{0} (intrinsicAbstractBase K) → Prop`,
and confirmed by `rfl` that each equals the displayed body written with fully
qualified names (`Langlands.NYLL.ClassFormation.baseField`,
`Langlands.NYLL.CyclicCohomology.extensionSubgroup`,
`Langlands.NYLL.ClassFormation.le_baseField`,
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.field`,
`Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois` and
`intrinsicAbstractBase`). The diagnostic is not part of this contribution.
Independent semantic acceptance and the proofs are separate obligations.
