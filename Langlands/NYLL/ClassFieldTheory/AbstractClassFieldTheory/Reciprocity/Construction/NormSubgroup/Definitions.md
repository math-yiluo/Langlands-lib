# NYLL M029: finite intermediate fields and the maximal unramified field

The paired Lean file ports three data declarations of the NYLL norm-subgroup
module: the finite intermediate field structure, its base instance, and the
maximal unramified field. The source is Naganori Yamaguchi's
ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`
(file SHA-256
`7d4c7c59cd25c27a728b49b8b4df61649bc818d2ef7ff4fdc375a92ea13f7460`). The
registered source `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Units

Adapted names use the prefix `Langlands.NYLL.ClassFormation.`. Original
names use the prefix `ClassFormation.`. The line ranges include the
docstrings.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M029.001 | `FiniteIntermediateField` | 34–45 (declaration at 36) | `FiniteIntermediateField` |
| M029.002 | `FiniteIntermediateField.base` | 49–64 (declaration at 50) | `FiniteIntermediateField.base` |
| M029.016 | `DegreeData.maximalUnramifiedField` | 204–208 (declaration at 206) | `DegreeData.maximalUnramifiedField` |

The section context of M029.001–002 is at source lines 18–32: `universe u`,
`namespace ClassFormation`, the opens `KummerTheory` and `CyclicCohomology`,
`noncomputable section`, `section finiteIntermediateFields` and the
variables `{G : Type u} [Group G] [TopologicalSpace G]`. M029.002 lies in
`namespace FiniteIntermediateField` (lines 47–66). M029.016 lies in
`section maximalUnramifiedFields` (line 198) with the same variables
(line 200), inside `namespace DegreeData` (line 202).

## The declarations

Every declaration takes implicit `{G : Type u}` and instance arguments
`[Group G] [TopologicalSpace G]`. A field is represented contravariantly by a
closed subgroup of `G`, Mathlib's `ClosedSubgroup G`; a larger field has a
smaller subgroup.

**`FiniteIntermediateField`** (M029.001) takes explicit
`(E K : ClosedSubgroup G)`, the subgroups of the top field `E` and the base
field `K`. It has exactly the four source fields:

- `field : ClosedSubgroup G`, the subgroup `G_M` of the intermediate field;
- `above : E.toSubgroup ≤ field.toSubgroup`, i.e. `G_E ≤ G_M`;
- `below : field.toSubgroup ≤ K.toSubgroup`, i.e. `G_M ≤ G_K`;
- `finite : Finite (K.toSubgroup ⧸ extensionSubgroup K field below)`, i.e.
  the coset space `G_K / G_M` is finite, so `M` has finite degree over `K`.

`extensionSubgroup` is the Library's
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`, that is, `G_L`
viewed as a subgroup of `G_K`. It is reached by name through
`open CyclicCohomology`, as in the source. No normality is required, so
`K.toSubgroup ⧸ …` is the coset space.

**`FiniteIntermediateField.base`** (M029.002) takes explicit
`(E K : ClosedSubgroup G)` and `(hEK : E.toSubgroup ≤ K.toSubgroup)` and
returns a `FiniteIntermediateField E K` with `field := K`, `above := hEK`,
`below := le_rfl`. Its `finite` field is the source tactic proof, kept
verbatim: it shows `extensionSubgroup K K le_rfl = ⊤` by extensionality, so
the quotient is by the whole group, and then `infer_instance` finds the
finiteness of that quotient.

**`DegreeData.maximalUnramifiedField`** (M029.016) takes explicit
`(D : DegreeData G)` and `(L : ClosedSubgroup G)` and returns the closed
subgroup `D.fieldInertia L`. `DegreeData` is the Library's
`Langlands.NYLL.ClassFormation.DegreeData` (M010.002), a continuous
surjective degree homomorphism `d : G → Ẑ`. `fieldInertia` is the Library's
`Langlands.NYLL.ClassFormation.DegreeData.fieldInertia` (M010.012), the
closed subgroup `L ⊓ D.inertia`, where `D.inertia` is the kernel of `d`. So
the maximal unramified extension of `L` is represented by `I_L = G_L ∩ ker d`.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- Only these three declarations are ported. The `infiniteNorms` section
  (lines 70–196) and the theorems after M029.016 are omitted from this
  module. M029.017–021, the theorems about `maximalUnramifiedField`, are
  separate statement units of this task.
- The two sections and their `variable` lines are kept with the same names
  and binders. They declare the same implicit `G` and instances, so every
  telescope is unchanged.
- `open KummerTheory` is omitted: no declaration here uses it, and the
  Library has no such namespace. `open CyclicCohomology` is kept for
  `extensionSubgroup`.
- The source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`
  and `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` are replaced by the
  focused Library imports
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`
  (for `DegreeData` and `fieldInertia`) and
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
  (for `extensionSubgroup`).

The universe `u`, binders, binder kinds, structure fields, docstrings and
bodies are otherwise unchanged, including the proof term in `base`. A
focused `lean_check` of this module reports no errors or warnings and the
single universe parameter `u`.

## Other modules of this task that use it

- `../ReciprocityIndependence/CompositumWith/Definitions.lean` ports
  M033.008 `FiniteIntermediateField.compositumWith`.
- `../FiniteIntermediateFieldCompositum/Definitions.lean` ports M037.001
  `FiniteIntermediateField.quotientCard`.

## Scope

These are data definitions only. No norm-subgroup, reciprocity,
class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
