# NYLL M032: finite field-extension bundles of cyclic subextensions

The paired Lean file ports two conversions of the NYLL unit-cohomology axiom
module. They turn a finite cyclic subextension, and a finite unramified
cyclic extension, into a `FiniteAbstractFieldExtension`, the bundle that
also records that the top field is finite over the distinguished base.
The source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`
(file SHA-256
`05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Units

Adapted names use the prefix `Langlands.NYLL.ClassFormation.`. Original
names use the prefix `ClassFormation.`. The line ranges include the
docstrings and attributes.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M032.005 | `FiniteCyclicSubextension.toFiniteAbstractFieldExtension` | 76–84 | `FiniteCyclicSubextension.toFiniteAbstractFieldExtension` |
| M032.010 | `FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension` | 121–127 | `FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension` |

The task does not list these two units. The listed target M032.011
(`FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension_isUnramifiedStatement`,
in the sibling module `FieldExtension/Statements.lean`) uses M032.010 by dot
notation, and M032.010 uses M032.005. The task requires porting such
unlisted declarations of the same source module, so both are ported here.

The section context is at source lines 18–34: `namespace ClassFormation`,
the opens `KummerTheory` and `CyclicCohomology`, `noncomputable section`,
`open CategoryTheory`, `universe u`, `section Generic` and
`variable {G : Type u} [Group G] [TopologicalSpace G]`. M032.005 lies in
`namespace FiniteCyclicSubextension` (lines 53–101), whose line 55 is
`variable {K : FiniteAbstractField G}`. The `Generic` section ends at
line 103. Lines 105–107 then bind `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]` and `{D : DegreeData G} {A : Rep ℤ G}`. M032.010 lies
in `namespace FiniteUnramifiedCyclicExtension` (lines 117–158), whose
line 119 is `variable {K : FiniteAbstractField G}`.

## The declarations

**`FiniteCyclicSubextension.toFiniteAbstractFieldExtension`** (M032.005).
This is a `noncomputable def` with the attribute `@[implicit_reducible]`
and the universe parameter `u`. Telescope: implicit `{G : Type u}`,
instances `[Group G] [TopologicalSpace G]`, implicit
`{K : FiniteAbstractField G}` and explicit `(E : FiniteCyclicSubextension K)`.
It returns a `FiniteAbstractFieldExtension G`. The body is the source tactic
block, unchanged: it makes the field `E.finite` a local instance of
`Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below)`
and returns `FiniteAbstractFieldExtension.ofInclusion E.field K E.below`.
That constructor is M010.131, published in the Library as
`Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.ofInclusion`.
It reads the finite relative quotient from that instance. So the result has

- top endpoint the finite abstract field with subgroup `E.field`. Its
  finiteness over the distinguished base is derived by `ofInclusion` from
  the finiteness of `L | K` and of `K` over the base, using the published
  tower identity for the degree cardinal;
- base endpoint `K`;
- inclusion `E.below`;
- relative finite quotient `E.finite`.

The normality, generator and generation fields of `E` are forgotten.

**`FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension`**
(M032.010). This is a `noncomputable def` with the attribute
`@[implicit_reducible]` and no universe parameters. Telescope: implicit
`{G : IntegralRepGroupType}`, instances `[Group G] [TopologicalSpace G]`,
implicit `{D : DegreeData G}`, implicit `{K : FiniteAbstractField G}` and
explicit `(E : FiniteUnramifiedCyclicExtension D K)`. It returns a
`FiniteAbstractFieldExtension G`, and its body is
`E.toFiniteCyclicSubextension.toFiniteAbstractFieldExtension`, so it applies
M032.005 to the parent cyclic subextension and forgets the unramifiedness
proof. `IntegralRepGroupType` is the Library's
`Langlands.NYLL.IntegralRepGroupType` (M002.001, the alias `Type 0`), so `G`
is in universe zero, as in the source. The variable `{D}` enters because the
type of `E` uses it. The variable `{A}` is unused and does not enter.

The other names are Library declarations: `FiniteAbstractField` (M010.121),
`FiniteAbstractFieldExtension` (M010.130), `extensionSubgroup` (M004.002,
`Langlands.NYLL.CyclicCohomology.extensionSubgroup`, reached through
`open CyclicCohomology` as in the source), `DegreeData`, and the M032
structures `FiniteCyclicSubextension` (M032.001) and
`FiniteUnramifiedCyclicExtension` (M032.009) of the sibling modules
`UnitCohomologyAxiom/CyclicSubextension/Definitions.lean` and
`UnitCohomologyAxiom/UnramifiedCyclic/Definitions.lean`.

## Modifications

Worker 5424 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- Only M032.005 and M032.010 are in this module, with the section,
  namespace and variable context they need. The other declarations of the
  source module are in the sibling modules named above, or are listed there
  as omitted. `open KummerTheory` is omitted because nothing here uses it.
  `open CategoryTheory` is kept as in the source, although nothing here
  uses it either.
- The source imports are replaced by two focused imports. One is the
  published `FiniteAbstractField/Extension/OfInclusion` module, for
  `FiniteAbstractFieldExtension` and `ofInclusion`. The other is the sibling
  module `UnitCohomologyAxiom/UnramifiedCyclic/Definitions.lean`, for both
  M032 structures, `extensionSubgroup` and `IntegralRepGroupType`.

Universes, binders, binder kinds, attributes, docstrings and bodies are
otherwise unchanged. A focused `lean_check` of this module reports no errors
or warnings. It reports the level parameter `u` for M032.005 and none for
M032.010.

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
