# NYLL M032.014: the absolute quotient of a finite unramified cyclic extension is finite

The paired Lean file adapts one anonymous instance of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`.
The pinned source file has SHA-256
`05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source declaration | Docstring | Declaration | Adapted name |
| --- | --- | --- | --- | --- |
| M032.014 | anonymous `noncomputable instance` in `ClassFormation.FiniteUnramifiedCyclicExtension` | 146 | 147–151 | `Langlands.NYLL.PortInternal.M032.d014` |

The source context is `namespace ClassFormation` (line 18),
`open KummerTheory` (line 20), `open CyclicCohomology` (line 22),
`noncomputable section` (line 26), `open CategoryTheory` (line 28),
`universe u` (line 30), the closed `section Generic` (lines 32–103), the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 106, after the comment line 105) and `{D : DegreeData G} {A : Rep ℤ G}`
(line 107), `namespace FiniteUnramifiedCyclicExtension` (line 117) and the
variable `{K : FiniteAbstractField G}` (line 119). The source imports are
the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements` and
`Nyll.GaloisCohomology.Cyclic.TateComparison` (lines 7–8). The other
declarations of the source file are outside this contribution.

The instance uses these published declarations:

- `FiniteUnramifiedCyclicExtension D K` (M032.009, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.UnramifiedCyclic.Definitions`),
  a finite cyclic subextension of `K` (closed subgroup `E.field` with
  `E.below : G_E ≤ G_K`, normal of finite cyclic index) that is unramified
  for `D`;
- the instances of that module and of the modules it imports, which make the
  quotient `G_K ⧸ G_E` finite (M032.013, published as
  `Langlands.NYLL.PortInternal.M032.d013`) and the absolute quotient of a
  finite abstract field `K` finite (M010.125, published as
  `Langlands.NYLL.PortInternal.M010.d125`);
- `relativeTowerQuotientFinite` (M026.014, proved in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`), whose type
  `relativeTowerQuotientFiniteStatement K L M hML hLK` states that
  `K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)` is finite when the
  two quotients `K ⧸ L` and `L ⧸ M` are (instance binders);
- `FiniteAbstractField G` (M010.121), `DegreeData G` (M010.002),
  `IntegralRepGroupType` (M002.001), `baseField G` and `le_baseField`
  (M010.003, M010.005) and `CyclicCohomology.extensionSubgroup` (M004.002),
  available through `open CyclicCohomology`.

The module imports
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.UnramifiedCyclic.Definitions`
and `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`.

## Instance and complete telescope

The instance has, before the binders shown, the binders of the source
variable lines 106, 107 and 119 that it uses: implicit
`{G : IntegralRepGroupType}`, the instances `[Group G]` and
`[TopologicalSpace G]`, and implicit `{D : DegreeData G}` and
`{K : FiniteAbstractField G}`. (`A` is not used.)

```lean
noncomputable instance _root_.Langlands.NYLL.PortInternal.M032.d014
    (E : FiniteUnramifiedCyclicExtension D K) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.field (le_baseField E.field)) :=
  relativeTowerQuotientFinite (baseField G) K.field E.field E.below
    (le_baseField K.field)
```

For a finite unramified cyclic extension `E` of a finite abstract field `K`,
the quotient of `(baseField G).toSubgroup` by `G_E` is finite: the tower
`G_E ≤ G_K ≤ G` has finite steps. The instance arguments of
`relativeTowerQuotientFinite` are found by instance resolution.

## Modifications

Worker 5264 made these changes:

1. Name the anonymous source instance
   `Langlands.NYLL.PortInternal.M032.d014` (declared with `_root_` inside the
   namespace), following the naming of the published sibling instances
   M032.012, M032.013 and M032.015 (`PortInternal.M032.d012`, `d013`,
   `d015`). It remains an instance.
2. Prefix the namespace with `Langlands.NYLL`.
3. Copy the docstring, the binders and the body verbatim.
4. Replace the source imports by the two focused published imports above
   and the source module docstring by a description of this module with a
   modification notice.
5. Keep the namespaces, both opens, the noncomputable section,
   `open CategoryTheory`, the comment line 105 and the variable lines 106,
   107 and 119; omit `universe u` (line 30) and the closed section `Generic`
   (lines 32–103), which the instance does not use, the declarations M032.010–.013
   of lines 121–144 (M032.012 and M032.013 are published) and the rest of
   the source file.
6. No helper declaration or linter option is added.

It discharges no host class-formation, cup, transfer, Tate or reciprocity
target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
