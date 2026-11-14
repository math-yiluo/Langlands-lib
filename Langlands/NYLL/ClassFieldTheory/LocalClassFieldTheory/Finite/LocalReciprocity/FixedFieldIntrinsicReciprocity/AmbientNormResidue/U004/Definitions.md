# Abelianized transport through an ambient presentation: definition

This module defines one declaration,
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.abelianizedTransport`.
It adapts source row M282.004, the definition
`LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.abelianizedTransport`,
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
Additive
  (Abelianization
    Gal(abstractRelativeFixedField K (SeparableClosure K)
      P.extension.below /
      abstractFixedField K (SeparableClosure K) P.base.field)) ≃+
  Additive (Abelianization Gal(E / F))
```

These are exactly the parameters of `fixedFieldQuotientEquiv` (M282.003):
the 22 parameters of the structure `AmbientEmbeddedFixedFieldPresentation`
(M282.002), with the three field types and the embedding `j` implicit, and the
presentation `P` explicit. All three field types are in universe zero, as in
the source. The compiled declaration was inspected with `#check` and
`#print axioms`: it has these parameters and this type, and it uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Meaning

Write `Ω = SeparableClosure K`. As explained for M282.003, a presentation `P`
records a finite quotient `Q = P.extension.extensionQuotient` of closed
subgroups of `Gal(Ω/K)`, and carries two group isomorphisms out of `Q`:

- `P.fixedFieldQuotientEquiv : Q ≃* Gal(Ω^{P.extension.field} / Ω^{P.base.field})`
  (M282.003), onto the Galois group of the two concrete fixed fields, written
  in Lean as `Gal(abstractRelativeFixedField K Ω P.extension.below /
  abstractFixedField K Ω P.base.field)`;
- the structure field `P.quotientEquiv : Q ≃* Gal(E / F)` (M282.002), onto the
  Galois group of the given extension, compatible with `j`.

The body applies Mathlib's `MulEquiv.abelianizationCongr` to both, turning a
group isomorphism `G ≃* H` into `Abelianization G ≃* Abelianization H`, then
`MulEquiv.toAdditive`, turning it into `Additive (Abelianization G) ≃+
Additive (Abelianization H)`. It composes the inverse of the first with the
second:

```lean
(P.fixedFieldQuotientEquiv.abelianizationCongr.toAdditive.symm).trans
  P.quotientEquiv.abelianizationCongr.toAdditive
```

So `abelianizedTransport P` sends an element of the additive abelianized
Galois group of the concrete fixed-field extension to the element of the
additive abelianization of `Gal(E / F)` that corresponds to it through the
common quotient `Q`. Here `Abelianization G` is Mathlib's abelianization
`G ⧸ commutator G`, and `Additive` is Mathlib's type synonym that writes the
group law additively.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M282.002, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation` (projections `base`, `extension`, `quotientEquiv`) | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U002.Definitions`, reached through the next import |
| M282.003, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.fixedFieldQuotientEquiv` | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.fixedFieldQuotientEquiv`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U003.Definitions` |
| M040.001, `ClassFormation.FiniteGaloisSubextension` (projection `below`), M040.004 `extensionQuotient` and M040.008 its group instance | The published declarations of module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`, reached through the M282.002 module |
| M010.121, `ClassFormation.FiniteAbstractField` (projection `field`) | `Langlands.NYLL.ClassFormation.FiniteAbstractField`, reached through the M282.002 module |
| M099.001, `LocalClassFieldTheory.abstractFixedField`, and M099.009, `LocalClassFieldTheory.abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` and `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField`, reached through the M282.003 module |
| Mathlib `Abelianization`, `MulEquiv.abelianizationCongr` (module `Mathlib.GroupTheory.Abelianization.Defs`), `Additive`, `MulEquiv.toAdditive`, `AddEquiv.symm`, `AddEquiv.trans`, `SeparableClosure`, `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.HasExtension`, `IsGalois` | Used unchanged |

At the time of staging, M282.003 is the candidate
`579eeb0a-3c89-40fd-b867-bb6d746d56c4`, not yet in the Library; the other
project declarations are published.

The module imports exactly the M282.003 module named in the table and
`Mathlib.GroupTheory.Abelianization.Defs`.

## Library search

The whole Library at commit `2d45c8a01a10b708df26d93cdde3c7e592664ab7` was
searched for `abelianizedTransport`, for every use of `abelianizationCongr`
and for every use of `AmbientEmbeddedFixedFieldPresentation`. The name does
not occur. Related uses of `abelianizationCongr` outside Mathlib include the
non-NYLL modules `Langlands/ClassFieldTheory/Local/IntermediateReciprocityTransport`,
`Langlands/ClassFieldTheory/Local/WeilReciprocityConjugation` and
`Langlands/ClassFieldTheory/Local/ReciprocityTransport`, which transport
along Weil-group and Galois-group isomorphisms unrelated to fixed-field
presentations, and in the proof of the published M288.001 theorem
`AmbientEmbeddedFixedFieldPresentation.quotientRestriction`, which defines no
equivalence. M260.006, M284.001 and the topological abelianization-transport
modules provide further related uses; none defines this presentation-specific
transport. The search found no existing implementation of M282.004.

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
| M282.004, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.abelianizedTransport` | docstring 133–135, signature 136–155, body 156–157 | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.abelianizedTransport` |

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
  listed above; the Mathlib abelianization import is kept.
- The source `open` lines are dropped. The definition refers to
  `AmbientEmbeddedFixedFieldPresentation`, `abstractRelativeFixedField` and
  `abstractFixedField`, which lie in the enclosing namespace
  `Langlands.NYLL.LocalClassFieldTheory`, and reaches every other project
  declaration through dot notation on `P`. The scoped notations opened by the
  source (`ValuativeRel`, `IsMulCommutative`) are not used.
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
source file, starting with `normResidueAbelianElement` (M282.005, docstring at line 159),
are separate units.
