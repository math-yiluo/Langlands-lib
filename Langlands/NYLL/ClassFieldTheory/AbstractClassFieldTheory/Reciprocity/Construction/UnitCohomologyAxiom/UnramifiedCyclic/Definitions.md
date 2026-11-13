# NYLL M032: finite unramified cyclic extensions

The paired Lean file ports the finite unramified cyclic extension structure of
the NYLL unit-cohomology axiom module and three of its anonymous instances.
The source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`
(file SHA-256
`05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Units

Adapted names use the prefix `Langlands.NYLL.ClassFormation.` unless written
in full. Original names use the prefix `ClassFormation.`. The line ranges
include the docstrings.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M032.009 | `FiniteUnramifiedCyclicExtension` | 109–115 | `FiniteUnramifiedCyclicExtension` |
| M032.012 | anonymous instance (normality) | 136–139 | `Langlands.NYLL.PortInternal.M032.d012` |
| M032.013 | anonymous instance (finiteness over `K`) | 141–144 | `Langlands.NYLL.PortInternal.M032.d013` |
| M032.015 | anonymous instance (`Fintype` over `K`) | 153–156 | `Langlands.NYLL.PortInternal.M032.d015` |

The section context is at source lines 18–30 (`namespace ClassFormation`,
the opens `KummerTheory` and `CyclicCohomology`, `noncomputable section`,
`open CategoryTheory`, `universe u`) and the variables of lines 105–107:
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{D : DegreeData G} {A : Rep ℤ G}`. Lines 117–119 open
`namespace FiniteUnramifiedCyclicExtension` with
`variable {K : FiniteAbstractField G}`; line 158 closes it.

## The declarations

**`FiniteUnramifiedCyclicExtension`** (M032.009). Telescope: implicit
`{G : IntegralRepGroupType}`, `[Group G] [TopologicalSpace G]`, explicit
`(D : DegreeData G)` and explicit `(K : FiniteAbstractField G)`.
`IntegralRepGroupType` is the Library's `Langlands.NYLL.IntegralRepGroupType`
(M002.001, the alias `Type 0`), so `G` is in universe zero, as in the
source. The explicit `D` is the structure's own parameter; the variable
`{D}` of line 107 is shadowed and does not enter, and `{A}` is unused. The
structure `extends FiniteCyclicSubextension K` (the M032.001 structure of the
sibling module `UnitCohomologyAxiom/CyclicSubextension/Definitions.lean`),
so it has all six fields of that structure, with the parent projection
`toFiniteCyclicSubextension`. It adds exactly one field,

- `unramified : toFiniteCyclicSubextension.IsUnramified D`,

which uses the M032.003 predicate
`FiniteCyclicSubextension.IsUnramified`: the underlying finite abstract
extension `L | K` is unramified for the degree datum `D`.

The three instances take implicit `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G] {D : DegreeData G} {K : FiniteAbstractField G}` and
explicit `(E : FiniteUnramifiedCyclicExtension D K)`:

- **`d012`** (M032.012) is the instance
  `(extensionSubgroup K.field E.field E.below).Normal := E.normal`.
- **`d013`** (M032.013) is the instance
  `Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := E.finite`.
- **`d015`** (M032.015) is the `noncomputable instance`
  `Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := Fintype.ofFinite _`.

Here `E.field`, `E.below`, `E.normal` and `E.finite` are the inherited fields
of the parent structure, and `extensionSubgroup` is the Library's
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), reached
through `open CyclicCohomology` as in the source.

## Modifications

Worker 5424 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- The anonymous instances get the required names
  `Langlands.NYLL.PortInternal.M032.d012`, `d013` and `d015`, declared with
  `_root_.` inside `namespace FiniteUnramifiedCyclicExtension`. Like the
  source instances they are global, with the same types and bodies; they
  repeat fields of the new structure.
- `open KummerTheory`, `universe u` and the `Generic` section are omitted:
  no declaration of this module uses them.
- The source imports are replaced by the single import of the sibling
  module `UnitCohomologyAxiom/CyclicSubextension/Definitions.lean`, which
  supplies `FiniteCyclicSubextension`, `FiniteAbstractField`,
  `DegreeData`, `extensionSubgroup` and `IntegralRepGroupType`.

Universes, binders, binder kinds, structure fields and bodies are otherwise
unchanged. A focused `lean_check` of this module reports no errors or
warnings and no universe parameters for `FiniteUnramifiedCyclicExtension`.

## Source declarations not in this module

- M032.010, `FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension`
  (lines 121–127), and the theorem M032.011,
  `toFiniteAbstractFieldExtension_isUnramified` (lines 129–134), use
  M032.005 and thus `FiniteAbstractFieldExtension.ofInclusion` (M010.131),
  which is not yet in the Library. They will be ported in a separate module
  of this task.
- M032.014, the anonymous instance of lines 146–151, is omitted. It gives
  finiteness of the absolute quotient
  `(baseField G).toSubgroup ⧸ extensionSubgroup (baseField G) E.field (le_baseField E.field)`
  by the source theorem `relativeTowerQuotientFinite` (M026.014), whose proof
  is not in the Library. No listed unit of this task uses this instance.
  In particular M032.015 needs only finiteness of the quotient over `K`,
  which M032.013 supplies.

## Scope

These are data definitions only. No host reciprocity, class-formation or
cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
