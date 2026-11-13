# NYLL M032: finite cyclic subextensions of a finite abstract field

The paired Lean file ports the finite cyclic subextension structure of the
NYLL unit-cohomology axiom module, its forgetful map, its ramification
predicates, its three anonymous instances and its fixed coefficient
representation. The source is Naganori Yamaguchi's ClassFieldTheory (NYLL)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`
(file SHA-256
`05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Units

Adapted names use the prefix `Langlands.NYLL.ClassFormation.` unless written
in full. Original names use the prefix `ClassFormation.`. The line ranges
include the docstrings and attributes.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M032.001 | `FiniteCyclicSubextension` | 36–51 | `FiniteCyclicSubextension` |
| M032.002 | `FiniteCyclicSubextension.toFiniteAbstractExtension` | 57–65 | `FiniteCyclicSubextension.toFiniteAbstractExtension` |
| M032.003 | `FiniteCyclicSubextension.IsUnramified` | 67–69 | `FiniteCyclicSubextension.IsUnramified` |
| M032.004 | `FiniteCyclicSubextension.IsTotallyRamified` | 71–74 | `FiniteCyclicSubextension.IsTotallyRamified` |
| M032.006 | anonymous instance (normality) | 86–89 | `Langlands.NYLL.PortInternal.M032.d006` |
| M032.007 | anonymous instance (finiteness) | 91–94 | `Langlands.NYLL.PortInternal.M032.d007` |
| M032.008 | anonymous instance (`Fintype`) | 96–99 | `Langlands.NYLL.PortInternal.M032.d008` |
| M032.016 | `FiniteCyclicSubextension.fixedRepresentation` | 164–169 | `FiniteCyclicSubextension.fixedRepresentation` |

The section context is at source lines 18–34: `namespace ClassFormation`,
the opens `KummerTheory` and `CyclicCohomology`, `noncomputable section`,
`open CategoryTheory`, `universe u`, `section Generic` and the variables
`{G : Type u} [Group G] [TopologicalSpace G]`. Lines 53–55 open
`namespace FiniteCyclicSubextension` with `variable {K : FiniteAbstractField G}`,
and lines 101–103 close it and the `Generic` section. M032.016 lies after
the variables of lines 105–107, `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]` and `{D : DegreeData G} {A : Rep ℤ G}`, inside the
reopened `namespace FiniteCyclicSubextension` with
`variable {K : FiniteAbstractField G}` (lines 160–162, closed at 171).

## The declarations

**`FiniteCyclicSubextension`** (M032.001). Telescope: implicit
`{G : Type u}`, instance arguments `[Group G] [TopologicalSpace G]`, and
explicit `(K : FiniteAbstractField G)`. It has exactly the six source
fields:

- `field : ClosedSubgroup G`, the closed subgroup representing the top field;
- `below : field.toSubgroup ≤ K.field.toSubgroup`;
- `normal : (extensionSubgroup K.field field below).Normal`;
- `finite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field field below)`;
- `generator : K.field.toSubgroup ⧸ extensionSubgroup K.field field below`;
- `generates : ∀ x, x ∈ Subgroup.zpowers generator`.

So the relative Galois quotient `G_K / G_L` is finite and cyclic, with a
chosen generator, and `G_L` is normal in `G_K`. `FiniteAbstractField` is the
Library's `Langlands.NYLL.ClassFormation.FiniteAbstractField` (M010.121, a
closed subgroup with finite quotient over the distinguished base field).
`extensionSubgroup` is the Library's
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`; it is reached by
name through `open CyclicCohomology`, as in the source.

The remaining declarations of the `Generic` section take implicit
`{G : Type u} [Group G] [TopologicalSpace G] {K : FiniteAbstractField G}` and
explicit `(E : FiniteCyclicSubextension K)`:

- **`toFiniteAbstractExtension`** (M032.002), with the source attribute
  `@[implicit_reducible]`, returns the Library's
  `Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension G`
  (M010.065) with `field := E.field`, `base := K.field`, `below := E.below`
  and `finiteQuotient := E.finite`. It forgets the generator and normality.
- **`IsUnramified`** (M032.003) takes a further explicit
  `(D : DegreeData G)` and is `E.toFiniteAbstractExtension.IsUnramified D`,
  the Library's `DegreeData.FiniteAbstractExtension.IsUnramified` (M010.071).
- **`IsTotallyRamified`** (M032.004) takes `(D : DegreeData G)` and is
  `E.toFiniteAbstractExtension.IsTotallyRamified D`, the Library's
  `DegreeData.FiniteAbstractExtension.IsTotallyRamified` (M010.072).
- **`d006`** (M032.006) is the instance
  `(extensionSubgroup K.field E.field E.below).Normal := E.normal`.
- **`d007`** (M032.007) is the instance
  `Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := E.finite`.
- **`d008`** (M032.008) is the `noncomputable instance`
  `Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := Fintype.ofFinite _`.

**`fixedRepresentation`** (M032.016). Telescope: implicit
`{G : IntegralRepGroupType}`, `[Group G] [TopologicalSpace G]`, implicit
`{K : FiniteAbstractField G}`, explicit `(E : FiniteCyclicSubextension K)` and
explicit `(A : Rep ℤ G)`. `IntegralRepGroupType` is the Library's
`Langlands.NYLL.IntegralRepGroupType` (M002.001, the alias `Type 0`), so here
the acting group is in universe zero, as in the source, because Mathlib's
`Rep ℤ G` needs that. The value has type
`Rep ℤ (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below)` and
is exactly `extensionFixedRepresentation A K.field E.field E.below E.normal`,
the Library's `Langlands.NYLL.CyclicCohomology.extensionFixedRepresentation`
(M004.003): restrict `A` to `G_K`, take the `G_L`-fixed vectors, and descend
the action to `G_K / G_L`. The source variables `{D}` and `{A}` of line 107
are not used by this definition (its explicit `A` shadows the variable), so
Lean does not add them to its telescope in the source either.

## Modifications

Worker 5424 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- The three anonymous instances get the required names
  `Langlands.NYLL.PortInternal.M032.d006`, `d007` and `d008`, declared with
  `_root_.` inside `namespace FiniteCyclicSubextension`. Like the source
  instances they are global instances, with the same types and bodies. They
  repeat structure fields of the new structure, so they cannot conflict with
  Mathlib or Library instances.
- `open KummerTheory` is omitted: no declaration of this module uses it.
- The variables of source lines 105–107 are placed in a
  `section IntegralRep`, and only `{G : IntegralRepGroupType} [Group G]
  [TopologicalSpace G]` are kept there. The source variables `{D}` and
  `{A}` do not enter any declaration of this module (see above), so every
  telescope is unchanged.
- M032.016 is moved next to the other `FiniteCyclicSubextension`
  declarations. In the source it follows the unramified cyclic extension
  declarations, which it does not use.
- The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
  and `Nyll.GaloisCohomology.Cyclic.TateComparison` are replaced by focused
  Library imports: the `FiniteAbstractField` module, the `FiniteExtension`
  definitions, the extension fixed-representation definitions and
  `IntegralRepUniverse`.

Universes, binders, binder kinds, attributes, structure fields and bodies are
otherwise unchanged. A focused `lean_check` of this module reports no errors
or warnings; it lists the single universe parameter `u` for
`FiniteCyclicSubextension` and none for `fixedRepresentation`.

## Source declarations not in this module

- M032.005, `FiniteCyclicSubextension.toFiniteAbstractFieldExtension`
  (lines 76–84), is not in this module. Its body uses
  `FiniteAbstractFieldExtension.ofInclusion` (M010.131), which is not yet in
  the Library. It will be ported in a separate module of this task together
  with M032.010 and M032.011, which use it.
- The unramified cyclic extension structure and its instances (M032.009,
  M032.012, M032.013, M032.015) are in the sibling module
  `UnitCohomologyAxiom/UnramifiedCyclic/Definitions.lean`.

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
