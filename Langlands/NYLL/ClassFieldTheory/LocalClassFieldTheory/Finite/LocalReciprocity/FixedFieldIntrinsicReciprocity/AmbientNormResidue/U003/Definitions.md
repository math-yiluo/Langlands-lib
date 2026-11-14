# The fixed-field quotient equivalence of an ambient presentation: definition

This module defines one declaration,
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.fixedFieldQuotientEquiv`.
It adapts source row M282.003, the definition
`LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.fixedFieldQuotientEquiv`,
and keeps its docstring, binders and body unchanged. The module installs no
instance and proves no theorem.

## Parameters and type

The definition takes, in the source order,

```lean
{K F E : Type}
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
{j : E →ₐ[K] SeparableClosure K}
(P : AmbientEmbeddedFixedFieldPresentation K F E j)
```

and has type

```lean
P.extension.extensionQuotient ≃*
  Gal(abstractRelativeFixedField K (SeparableClosure K)
    P.extension.below /
    abstractFixedField K (SeparableClosure K) P.base.field)
```

The 22 parameters before `P` are those of the structure
`AmbientEmbeddedFixedFieldPresentation` (M282.002), with the three field
types and the embedding `j` made implicit, as in the source; only the
presentation `P` is explicit. All three field types are in universe zero, as in
the source. The compiled declaration was inspected with the Lean service: it
is a definition with these parameters and this type, and it uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Meaning

Write `Ω = SeparableClosure K` and `G = Gal(Ω/K)`. A presentation `P`
supplies a closed subgroup `P.base.field` of `G` and a finite Galois
subextension `P.extension` of it: a closed subgroup
`P.extension.field ≤ P.base.field`, with proof `P.extension.below` of the
inclusion and proof `P.extension.normal` that the corresponding subgroup of
`P.base.field` is normal. The type `P.extension.extensionQuotient` is the
finite quotient `P.base.field / P.extension.field`, with the group structure
of the published instance `extensionQuotient_groupInstance`.

The target is the Galois group of the concrete field extension
`Ω^{P.extension.field} / Ω^{P.base.field}`: here
`abstractFixedField K Ω P.base.field` is the fixed field of `P.base.field`, and
`abstractRelativeFixedField K Ω P.extension.below` is the fixed field of
`P.extension.field`, viewed as an intermediate field over that fixed field.
`Gal(A / B)` is Mathlib's notation for `A ≃ₐ[B] A`.

The body is the composite of two published group isomorphisms:

1. `P.extension.extensionQuotientMulEquiv`, the identity isomorphism
   (`MulEquiv.refl`) from `P.extension.extensionQuotient` to the underlying
   quotient `P.base.field.toSubgroup ⧸ extensionSubgroup P.base.field
   P.extension.field P.extension.below`;
2. `abstractExtensionQuotientEquivGaloisGroup K Ω P.base.field
   P.extension.field P.extension.below P.extension.normal`, the canonical
   isomorphism from that quotient to the Galois group above.

So `fixedFieldQuotientEquiv P` identifies the abstract quotient recorded by the
presentation with the Galois group of the two concrete fixed fields. It does
not use the presentation's own isomorphism `P.quotientEquiv` with `Gal(E/F)`
or any other field of `P` beyond `P.base` and `P.extension`.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M282.002, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation` (projections `base`, `extension`) | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U002.Definitions` |
| M010.121, `ClassFormation.FiniteAbstractField` (projection `field`) | `Langlands.NYLL.ClassFormation.FiniteAbstractField`, reached through the M282.002 module |
| M040.001, `ClassFormation.FiniteGaloisSubextension` (projections `field`, `below`, `normal`) | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`, reached through the M282.002 module |
| M040.004, `ClassFormation.FiniteGaloisSubextension.extensionQuotient` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotient`, same module |
| M040.008, `ClassFormation.FiniteGaloisSubextension.extensionQuotient_groupInstance` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotient_groupInstance`, same module, found by instance search |
| M040.010, `ClassFormation.FiniteGaloisSubextension.extensionQuotientMulEquiv` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotientMulEquiv`, same module |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`, reached through the next import |
| M099.009, `LocalClassFieldTheory.abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions`, reached through the next import |
| M099.017, `LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup` | `Langlands.NYLL.LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Equivalences.Definitions` |
| Mathlib `SeparableClosure`, `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.HasExtension`, `IsGalois`, `AlgEquiv`, `MulEquiv.trans` | Used unchanged |

The normality argument of M099.017 has type
`(L.toSubgroup.subgroupOf K.toSubgroup).Normal`; the field
`P.extension.normal` has type
`(extensionSubgroup P.base.field P.extension.field P.extension.below).Normal`,
and Lean accepts it there unchanged, as in the source. Likewise the target of
step 1 is accepted as the source of step 2 without a cast.

The module imports exactly the two published modules named in the table for
M282.002 and M099.017.

## Library search

The whole Library at commit `58ad0f796899b4aa457077d0146815c24758f739` was
searched for `fixedFieldQuotientEquiv` and for every use of
`abstractExtensionQuotientEquivGaloisGroup`. The name occurs only in the
Scope paragraph of the M282.002 Markdown, which names this unit as separate.
The equivalence is used only in its own module and in the statement module
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits/Action/Statements`,
which applies it to explicit closed subgroups and defines no equivalence for a
presentation. So nothing in the Library already covers M282.003.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean>).
The complete file was read; its SHA-256 is
`68d2430b93071e1b8d5a021fef789a2548146fc18d268ac2887fc4710d2d08dc`.
The header is at lines 1–5, the imports at 7–9, the module docstring at
11–18, `noncomputable section` at 22, the namespace at 24, the `open` lines at
26–29 and the nested `namespace AmbientEmbeddedFixedFieldPresentation` at 106.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M282.003, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.fixedFieldQuotientEquiv` | docstring 108–109, signature 110–127, body 128–131 | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.fixedFieldQuotientEquiv` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the definition directly from the pinned original on
14 November 2026 and made these changes:

- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix; the
  nested namespace `AmbientEmbeddedFixedFieldPresentation` is kept. The name,
  docstring, binders and body are unchanged.
- The source imports (the NYLL `EmbeddedFrobeniusTransport` module,
  `Mathlib.FieldTheory.Galois.Abelian` and
  `Mathlib.GroupTheory.Abelianization.Defs`) are replaced by the two imports
  listed above.
- The source `open` lines are dropped. The definition refers to
  `AmbientEmbeddedFixedFieldPresentation`, `abstractRelativeFixedField`,
  `abstractFixedField` and `abstractExtensionQuotientEquivGaloisGroup`, which
  all lie in the enclosing namespace `Langlands.NYLL.LocalClassFieldTheory`,
  and reaches the `ClassFormation` declarations only through dot notation on
  `P.extension`. The scoped notations opened by the source (`ValuativeRel`,
  `IsMulCommutative`) are not used.
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

This unit contains only this definition. The later declarations of the
source file, starting at line 133, are separate units.
