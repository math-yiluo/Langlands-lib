# Abstract reciprocity: the class field axiom

This module ports the two NYLL source declarations M072.001 and M072.002: the
proposition-valued structure `ClassFieldAxiomCohomologyData` and the
predicate `SatisfiesClassFieldAxiom`. They contain no proof obligations of
their own; the three source theorems about them are the targets of the sibling
module `ClassFieldAxiom/Statements`.

## Original source

Adapted by Worker 90 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean>)
(SHA-256 `5251ee8dafd55cbbf1dc7258b7a0a577b2a2b3c1d9a4f020f4afce8013211814`).
The registered source collection is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M072.001 | `ClassFormation.ClassFieldAxiomCohomologyData`, docstring 36–37, structure 38–51 | `Langlands.NYLL.ClassFormation.ClassFieldAxiomCohomologyData` |
| M072.002 | `ClassFormation.SatisfiesClassFieldAxiom`, docstring 53–59, definition 60–62 | `Langlands.NYLL.ClassFormation.SatisfiesClassFieldAxiom` |

The source module docstring (lines 9–17), the namespace and `open` lines
(19, 21, 27), `noncomputable section` (25), the universe comment (29–32) and
the section variable line 34
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` are
retained.

## The declarations

Throughout, `G : IntegralRepGroupType` is a group in `Type 0` with a
topology; `IntegralRepGroupType` is the published alias
`Langlands.NYLL.IntegralRepGroupType := Type 0`, the universe forced by
Mathlib's `Rep ℤ G`. `A : Rep ℤ G` is an integral representation,
`K : FiniteAbstractField G` a closed subgroup of finite index over the
distinguished base field `baseField G = ⊤`, and
`E : FiniteCyclicSubextension K` a closed subgroup `E.field ≤ K.field`,
normal in `K.field`, with finite cyclic quotient
`Q = K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below` and a
chosen generator.

- `ClassFieldAxiomCohomologyData A K E : Prop` is a structure with four
  fields: `finiteTateHZero : Finite (tateCohomology (E.fixedRepresentation A) 0)`,
  `finiteTateHMinusOne : Finite (tateCohomology (E.fixedRepresentation A) (-1))`,
  `tateHZero_card : Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
  (E.toFiniteAbstractExtension.degree : ℕ)` and
  `tateHMinusOne_card : Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1`.
  Here `E.fixedRepresentation A` is the actual `Q`-representation on the
  `E.field`-invariants of `A` restricted to `K.field`, and
  `tateCohomology` is Mathlib's Tate cohomology of a representation of the
  finite group `Q` (its `Fintype` instance comes from the finite cyclic
  subextension). `E.toFiniteAbstractExtension.degree : ℕ+` is the index of
  `E.field` in `K.field`, the degree `[L : K]`. Both finiteness fields
  are stored before the cardinalities, since `Nat.card` of an infinite type
  is `0`.
- `SatisfiesClassFieldAxiom A : Prop` is
  `∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
  ClassFieldAxiomCohomologyData A K E`: the class-field axiom
  `#Ĥ⁰(G(L/K), A_L) = [L : K]`, `#Ĥ⁻¹(G(L/K), A_L) = 1` for every finite
  cyclic `L / K` with `K` finite over the base.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M002.001, `IntegralRepGroupType` | `Langlands.NYLL.IntegralRepGroupType`, module `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse` |
| M010.121, `ClassFormation.FiniteAbstractField` | `Langlands.NYLL.ClassFormation.FiniteAbstractField`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions` |
| M032.001, `ClassFormation.FiniteCyclicSubextension` | `Langlands.NYLL.ClassFormation.FiniteCyclicSubextension`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.CyclicSubextension.Definitions` |
| M032.002, `FiniteCyclicSubextension.toFiniteAbstractExtension` | `Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.toFiniteAbstractExtension`, same module |
| M032.006, M032.008, anonymous `Normal` and `Fintype` instances of a finite cyclic subextension | `Langlands.NYLL.PortInternal.M032.d006`, `Langlands.NYLL.PortInternal.M032.d008`, same module |
| M032.016, `FiniteCyclicSubextension.fixedRepresentation` | `Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.fixedRepresentation`, same module |
| M010.085, `DegreeData.FiniteAbstractExtension.degree` | `Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.degree`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions` |

`tateCohomology` and `Nat.card` are Mathlib's. No new instance is declared.

## Modifications

Worker 90 made these changes:

- The namespace `ClassFormation` is prefixed with `Langlands.NYLL`.
- The source import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  is replaced by the published Library modules listed above and the Mathlib
  module `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`.
- A modification paragraph is added to the module docstring.
- The three source theorems of lines 64–98 are moved to the sibling
  statements module as Prop-valued targets.

The structure (its `Prop` sort, binders, field names, field types and
docstrings) and the predicate body are unchanged.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records these modifications. The Library's
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned upstream
files (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This NYLL-internal class-field axiom is not the host class-formation
predicate, and this support unit makes no claim to discharge the host
class-formation, cup, transfer, Tate or reciprocity targets.
