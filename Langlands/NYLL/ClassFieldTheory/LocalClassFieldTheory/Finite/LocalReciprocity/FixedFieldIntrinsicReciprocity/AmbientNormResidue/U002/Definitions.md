# Ambient fixed-field presentations of embedded Galois extensions: definition

This module defines one structure,
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation`,
together with the projections, constructor and other auxiliary declarations
that Lean generates for every structure. It adapts source row M282.002, the
structure `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation`,
keeping its parameters, docstrings and fields unchanged. The module installs
no instance, constructs no element of the structure and proves no theorem.

## Parameters

The structure takes, in the source order,

```lean
(K F E : Type)
[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]
[Field E] [Algebra K F] [Algebra F E] [Algebra K E]
[IsScalarTower K F E]
[FiniteDimensional K F] [Algebra.IsSeparable K F]
[Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
[FiniteDimensional F E] [IsGalois F E]
(j : E →ₐ[K] SeparableClosure K)
```

and lives in `Type`. These are the 22 parameters of the published
abbreviation `ambientEmbeddedSeparableClosureEquiv` (M282.001), in the same
order. `K` and `F` are nonarchimedean local fields (Mathlib's root class
`IsNonarchimedeanLocalField`), `F` is a finite separable extension of `K`
whose valuation extends that of `K`, `E` is a finite Galois extension of `F`
in a scalar tower `K ⊆ F ⊆ E`, and `j` is a `K`-algebra embedding of `E` into
Mathlib's separable closure `SeparableClosure K`. All three field types are in
universe zero, as in the source.

## Fields

Write `Ω = SeparableClosure K` and `G = Gal(Ω/K)`. For a closed subgroup `H`
of `G`, `abstractFixedField K Ω H` is its fixed field. The fields are:

| Field | Type | Meaning |
| --- | --- | --- |
| `baseEmbedding` | `F →ₐ[K] Ω` | An embedding of the base field into `Ω` |
| `base` | `FiniteAbstractField G` | A closed subgroup `base.field` of `G` together with finiteness of `G / base.field` |
| `extension` | `FiniteGaloisSubextension base.field` | A closed subgroup `extension.field ≤ base.field`, normal in `base.field` with finite quotient |
| `baseEmbedding_eq` | `baseEmbedding = j.comp (IsScalarTower.toAlgHom K F E)` | The base embedding is `j` restricted to `F` |
| `base_field_eq` | `base.field = closedFixingSubgroup K Ω (AlgHom.fieldRange baseEmbedding)` | `base.field` is the subgroup fixing the image of `F` |
| `extension_field_eq` | `extension.field = closedFixingSubgroup K Ω (AlgHom.fieldRange j)` | `extension.field` is the subgroup fixing the image of `E` |
| `baseEquiv` | `F ≃ₐ[K] abstractFixedField K Ω base.field` | A `K`-algebra isomorphism of `F` with the fixed field of `base.field` |
| `baseEquiv_apply` | `∀ x : F, ((baseEquiv x : abstractFixedField K Ω base.field) : Ω) = baseEmbedding x` | `baseEquiv` followed by the inclusion into `Ω` is `baseEmbedding` |
| `quotientEquiv` | `extension.extensionQuotient ≃* Gal(E / F)` | A group isomorphism of the finite quotient `base.field / extension.field` with `Gal(E/F)` |
| `quotientEquiv_mk_apply` | `∀ (sigma : base.field.toSubgroup) (x : E), j (quotientEquiv (extension.extensionQuotientMk sigma) x) = sigma.1 (j x)` | The quotient isomorphism is compatible with `j`: the class of `sigma` acts on `E` as `sigma` acts on `j(E)` |

So an element records how `E / F` is realized inside `Ω` by fixed fields:
`base.field` is the absolute Galois group of the image of `F`,
`extension.field` that of the image of `E`, `F` is identified with the
fixed field of `base.field`, and the finite quotient
`base.field / extension.field` is identified with `Gal(E/F)` compatibly with
`j`. The structure only bundles these data and conditions; it does not
assert that such a presentation exists.

In the field types, `Gal(E / F)` is Mathlib's notation for `E ≃ₐ[F] E`.
`extension.extensionQuotient` is the published
`FiniteGaloisSubextension.extensionQuotient`, the quotient type
`base.field.toSubgroup ⧸ extensionSubgroup base.field extension.field _`, with
the group structure of the published instance
`FiniteGaloisSubextension.extensionQuotient_groupInstance`.
`extension.extensionQuotientMk` is the published quotient homomorphism
`base.field.toSubgroup →* extension.extensionQuotient`.
`closedFixingSubgroup K Ω M` is the fixing subgroup of the intermediate
field `M`, bundled as a closed subgroup; it needs `IsGalois K Ω`, which
Mathlib provides as an instance for the separable closure (module
`Mathlib.FieldTheory.IsSepClosed`).

The compiled structure was inspected with `#print`: it has 22 parameters
and exactly the ten fields above, with these types.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M010.121, `ClassFormation.FiniteAbstractField` (and its projection `field`) | `Langlands.NYLL.ClassFormation.FiniteAbstractField`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions` |
| M040.001, `ClassFormation.FiniteGaloisSubextension` (and its projection `field`) | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions` |
| M040.004, `ClassFormation.FiniteGaloisSubextension.extensionQuotient` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotient`, same module |
| M040.008, `ClassFormation.FiniteGaloisSubextension.extensionQuotient_groupInstance` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotient_groupInstance`, same module, found by instance search |
| M040.011, `ClassFormation.FiniteGaloisSubextension.extensionQuotientMk` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk`, same module |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup`, module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`, reached through the next import |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |
| Mathlib `SeparableClosure`, `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.HasExtension`, `IsGalois`, `AlgHom.fieldRange`, `IsScalarTower.toAlgHom`, `AlgEquiv`, `MulEquiv` | Used unchanged |

The module imports `Mathlib.FieldTheory.IsSepClosed`,
`Mathlib.NumberTheory.LocalField.Basic` and
`Mathlib.RingTheory.Valuation.Extension` (as for M282.001), and the three
published modules named in the table that define `FiniteAbstractField`,
`FiniteGaloisSubextension` and `abstractFixedField`.

## Library search

The whole Library at commit `451cce4ca176c34856be86a36801b7a3b585ae77` was
searched for `AmbientEmbeddedFixedFieldPresentation`, for structures whose
names end in `Presentation`, and for `closedFixingSubgroup` and
`AlgHom.fieldRange` used together with `SeparableClosure`. No structure
bundles a fixed-field presentation. The only such combination is the
statement module `BaseComparison/IntrinsicBaseEquivalence/U001/Statements`,
which asserts finiteness for `closedFixingSubgroup K (SeparableClosure K)
(AlgHom.fieldRange i)` and records no presentation data. So nothing in the
Library already covers M282.002.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean>).
The complete file was read; its SHA-256 is
`68d2430b93071e1b8d5a021fef789a2548146fc18d268ac2887fc4710d2d08dc`.
The header is at lines 1–5, the imports at 7–9, the module docstring at
11–18, `noncomputable section` at 22, the namespace at 24 and the `open`
lines at 26–29.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M282.002, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation` | docstring 51–56, parameters 57–69, fields 70–104 | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the structure directly from the pinned original on
13 November 2026 and made these changes:

- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
  The name, docstrings, parameters and fields are unchanged.
- The source imports (the NYLL `EmbeddedFrobeniusTransport` module,
  `Mathlib.FieldTheory.Galois.Abelian` and
  `Mathlib.GroupTheory.Abelianization.Defs`) are replaced by the six imports
  listed above.
- The source `open` lines are replaced by
  `open Langlands.NYLL.RamificationTheory Langlands.NYLL.ClassFormation`,
  the opened namespaces whose names (`closedFixingSubgroup`,
  `FiniteAbstractField`, `FiniteGaloisSubextension`) the structure uses.
  The scoped notations opened by the source (`ValuativeRel`,
  `IsMulCommutative`) are not used by the structure.
- All other declarations of the source file are omitted.

No instance or simp attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this structure. The declarations in its namespace,
starting with `fixedFieldQuotientEquiv` (M282.003, line 110), and all later
declarations of the source file are separate units.
