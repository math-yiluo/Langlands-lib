# NYLL M039.018: a finite field as a finite intermediate field of its maximal unramified extension

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`.
The pinned source file has SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.DegreeData.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M039.018 | `fieldAsMaximalUnramifiedIntermediate` | 233 | 234–237 | 238–241 | `fieldAsMaximalUnramifiedIntermediate` |

The source file imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup`
and `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse` (lines 7–8). The
context of the definition is `universe u` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` (line 22),
`open CyclicCohomology` (line 24), `noncomputable section` (line 28), the
section `finiteIntermediateField` (lines 227 and 245) with its variable line
229,

```lean
variable {G : Type u} [Group G] [TopologicalSpace G]
```

`namespace DegreeData` (lines 231 and 243), and the closing lines 308–309.
The port keeps this context in the same order and omits `open KummerTheory`,
which the definition does not use.

The names used resolve to published `Langlands.NYLL` declarations, all
imported through
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`: the structure
`ClassFormation.FiniteIntermediateField E K` (M029.001, in that module) of a
closed subgroup `field` with `above : E.toSubgroup ≤ field.toSubgroup`,
`below : field.toSubgroup ≤ K.toSubgroup` and finiteness of
`K.toSubgroup ⧸ extensionSubgroup K field below`; the maximal unramified
field `ClassFormation.DegreeData.maximalUnramifiedField` (M029.016, in that
module); `ClassFormation.DegreeData` (M010.002) and
`ClassFormation.DegreeData.fieldInertia` (M010.012), both in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`; and
`CyclicCohomology.extensionSubgroup` (M004.002, in
`Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
found through `open CyclicCohomology`). Mathlib supplies `ClosedSubgroup`,
quotient groups, `Finite` and `inf_le_left`.

The source field `above := D.maximalUnramifiedField_le L` uses M029.019,
whose proof is not published.

The source proof of M029.019
`DegreeData.maximalUnramifiedField_le` (`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean`, docstring line 227,
theorem lines 228–231) is

```lean
theorem maximalUnramifiedField_le (D : DegreeData G) (L : ClosedSubgroup G) :
    (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact inf_le_left
```

where M029.017 `maximalUnramifiedField_eq_fieldInertia` (lines 213–216) is
the equation `D.maximalUnramifiedField L = D.fieldInertia L`, proved by
`rfl`. Neither proof is published. The published definitions make
`D.maximalUnramifiedField L` (M029.016) equal by definition to
`D.fieldInertia L` (M010.012), the closed subgroup `L ⊓ D.inertia`. The
port therefore writes the term

```lean
show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
  inf_le_left
```

in place of `D.maximalUnramifiedField_le L`: `show` states the source
proposition of M029.019, and Lean checks `inf_le_left` against it by
definitional unfolding, which replaces the `rfl` rewrite. Mathlib supplies
`ClosedSubgroup`, its lattice structure and `inf_le_left`.

## Definition

The definition has the section binders implicit `{G : Type u}`,
`[Group G]` and `[TopologicalSpace G]`, followed by the binders shown.

```lean
/-- `L` itself is a finite intermediate field of `\widetilde L | K`. -/
def fieldAsMaximalUnramifiedIntermediate (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteIntermediateField (D.maximalUnramifiedField L) K where
  field := L
  above := show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from
    inf_le_left
  below := hLK
  finite := hfinite
```

For closed subgroups `K` and `L` with `G_L ≤ G_K` and `G_K / G_L` finite,
the definition presents `L` as a finite intermediate field of
`\widetilde L | K`: its field is `L`, it lies above `\widetilde L` because
the subgroup `L ⊓ D.inertia` of `\widetilde L` lies in `G_L`, it lies below
`K` by `hLK`, and the
finiteness field is the instance `hfinite`. Only the proof field `above`
differs from the source term, and by proof irrelevance the structure value
is the source one.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.DegreeData.fieldAsMaximalUnramifiedIntermediate`.
2. Replace the field proof `above := D.maximalUnramifiedField_le L` by
   `above := show (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup from`
   followed by `inf_le_left` on the next line, as explained above.
3. Copy the docstring, the binders and the other three fields verbatim; a
   line diff against the pinned source shows no other difference.
4. Replace the two source imports by the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`, and the
   source module docstring by a description of this module with a
   modification notice.
5. Keep the source context listed above, without `open KummerTheory`; omit
   the other declarations of the source file. No helper declaration,
   instance or linter option is added.

This is a definition only. It discharges no host class-formation, Tate or
reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), together with the other five
modules of this contribution, with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
