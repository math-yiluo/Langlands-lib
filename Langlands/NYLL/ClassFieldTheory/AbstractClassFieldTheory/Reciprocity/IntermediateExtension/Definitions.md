# NYLL M076: intermediate-extension subgroup, coset and upper-quotient data

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
(file SHA-256 `f031b91cd496accfb520a0665cbb59f5f8a4ac0f567ee2c5a5dffc408ef05b44`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

All adapted names use the prefix
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.`, and all original
names the prefix `ClassFormation.FiniteGaloisSubextension.`.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M076.001 | `intermediateSubgroup` | 43–45 | `intermediateSubgroup` | def |
| M076.004 | `intermediateCoset` | 72–74 | `intermediateCoset` | def |
| M076.037 | `upperQuotient` | 482–484 | `upperQuotient` | def |
| M076.038 | `upperQuotient_groupInstance` | 487–491 | `upperQuotient_groupInstance` | instance |
| M076.039 | `upperQuotientMulEquiv` | 494–497 | `upperQuotientMulEquiv` | def |
| M076.040 | `upperQuotientMk` | 500–503 | `upperQuotientMk` | def |

These units use no other declaration of the source module. The private
source definition `representativeIntermediateCoset` (lines 78–82) is used only
inside source proofs and is not ported.

## Telescope and objects

The surrounding source scaffolding is kept: `namespace ClassFormation`
(line 26), `open CyclicCohomology` (30), `noncomputable section` (34),
`variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
(36), `namespace FiniteGaloisSubextension` (38) and
`variable {K : ClosedSubgroup G}` (40). As in the source, Lean includes in a
definition only the section variables it uses, so none of these six
declarations takes `[IsTopologicalGroup G]`; a `#check` of each confirmed the
telescopes below, with the single universe parameter `u_1` of `Type*`.

- `intermediateSubgroup`: `{G : Type u_1} [Group G] [TopologicalSpace G]
  {K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
  (S : Subgroup L.extensionQuotient) : Subgroup K.toSubgroup`, with source
  body `by exact S.comap L.extensionQuotientMk`, the inverse image of `S` under
  the canonical projection `G_K → G(L/K)`.
- `intermediateCoset`: the same first five binders, then
  `(q : L.extensionQuotient) : Set K.toSubgroup`, with body
  `{x | L.extensionQuotientMk x = q}`, the fibre of the projection over `q`.
- `upperQuotient`: binders through `(S : Subgroup L.extensionQuotient)`,
  result `Type _` (elaborated to `Type u_1`), body
  `L.extensionQuotient ⧸ S`, a named `def` boundary.
- `upperQuotient_groupInstance`: binders through `S`, then the anonymous
  instance binder `[S.Normal]`, giving `Group (L.upperQuotient S)` by
  `change Group (L.extensionQuotient ⧸ S)` and `infer_instance`, as in the
  source. It is the only instance, in the source scope.
- `upperQuotientMulEquiv`: binders through `[S.Normal]`, type
  `L.upperQuotient S ≃* (L.extensionQuotient ⧸ S)`, body `MulEquiv.refl _`.
- `upperQuotientMk`: binders through `[S.Normal]`, type
  `L.extensionQuotient →* L.upperQuotient S`, body `QuotientGroup.mk' S`.

## Reused declarations

From the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`
(port of M040): the structure `FiniteGaloisSubextension` (M040.001), its
`extensionQuotient` (M040.004) with group instance (M040.008), and
`extensionQuotientMk` (M040.011). Mathlib supplies `Subgroup.comap`,
`QuotientGroup.mk'`, `MulEquiv.refl`, and the quotient group by a normal
subgroup.

## Modifications

Worker 4918 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. The source import
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension`
   is replaced by its port
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`;
   the source import `Mathlib.Topology.Algebra.Group.Basic` is kept.
3. `open KummerTheory` (line 28) is dropped: none of these declarations uses
   a name from it, and no such namespace is imported, so the command would not
   elaborate. `open CyclicCohomology` is kept and resolves to
   `Langlands.NYLL.CyclicCohomology`.
4. The source theorems, the private helpers, and the data commands not in
   the table (`intermediateField`, `intermediateFiniteAbstractExtension`,
   `lowerFiniteGalois`, `intermediateFiniteGalois`, `lowerRestrictionHom`,
   `lowerQuotientEquiv`, `upperQuotientEquiv` and the other instances) are
   omitted; they are routed to sibling tasks or later. The listed theorems
   M076.002, 006, 009, 011, 012, 023 and 034 are stated as Prop-valued targets
   in the sibling `Statements` module.
5. The source module docstring (lines 10–24) is replaced by a short
   docstring recording these modifications.

Declarations, binders, docstrings and bodies are otherwise unchanged.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
