# NYLL M028.007 and M028.008: prime elements and the additive unit group

The paired Lean file adapts two definitions from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`.
The pinned source file has SHA-256
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source declaration | Docstring | Command | Adapted declaration |
| --- | --- | --- | --- | --- |
| M028.007 | `ClassFormation.ValuationData.IsPrimeElement` (def, `Prop`) | 121 | 122–124 | `Langlands.NYLL.ClassFormation.ValuationData.IsPrimeElement` |
| M028.008 | `ClassFormation.ValuationData.unitAddSubgroup` (def) | 126–127 | 128–130 | `Langlands.NYLL.ClassFormation.ValuationData.unitAddSubgroup` |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), the comment and variables at lines 26–28,
and `namespace ValuationData` (line 107). Both source docstrings are retained
verbatim.

The definitions use these published `Langlands.NYLL` declarations:
`ClassFormation.ValuationData` (M025.012), `ClassFormation.ValuationData.valueGroup`
(M025.013), `ClassFormation.ValuationData.valuationAt` (M025.025, in
`Degree.Valuation.ValuationData.Normalized.Definitions`),
`ClassFormation.ValuationData.oneValue` (M028.005, in
`Degree.PrimeElements.OneValue.Definitions`), `ClassFormation.FiniteAbstractField`
(M010.121), `ClassFormation.DegreeData` (M010.002),
`KummerTheory.ambientFixedAddSubgroup` (M023.001, hence the source open of
`KummerTheory`) and `IntegralRepGroupType` (M002.001). `AddSubgroup`,
`AddMonoidHom.ker` and `Rep` are Mathlib's.

## Objects and complete telescopes

Both definitions have the source section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the explicit binders shown. The group lies in `Type 0`; the carrier of `A`
has an arbitrary universe, the single universe parameter. Write
`A_K = ambientFixedAddSubgroup A K.field` for the additive subgroup of
`G_K`-fixed vectors of `A`, where `K.field` is the closed subgroup `G_K`.

```lean
def IsPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G)
    (π : ambientFixedAddSubgroup A K.field) : Prop :=
  v.valuationAt K π = v.oneValue
```

`π ∈ A_K` is a prime element of `K` when its normalized valuation
`v_K π ∈ Z` is the element `1` of the value group `Z = v(A_k)`. Here
`v.valuationAt K : A_K →+ v.valueGroup` is the normalized valuation
`(1/f_K) v ∘ N_{K|k}`, and `v.oneValue` is `1 : ZHat` bundled as an element
of `v.valueGroup`. The equation is an equality in the subtype
`v.valueGroup`.

```lean
def unitAddSubgroup (v : ValuationData D A) (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  (v.valuationAt K).ker
```

The additive unit group `U_K` of `K` is the kernel of the normalized
valuation, the additive subgroup of `A_K` of elements with
`v_K u = 0`. In the multiplicative language of the source this is
`U_K = {u | v_K(u) = 0}`.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace the source import of `Degree.ValuationLaws` (line 7) by the two
   focused imports
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`
   (for `valuationAt`) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions`
   (for `oneValue`).
3. Retain both opens, the noncomputable section, the group-variable comment
   and both variable lines in their source order (before
   `namespace ValuationData`). Replace the source module docstring by a
   description of this module with a modification notice.
4. Extract only these two definitions; their kinds, binders, types, bodies
   and docstrings are unchanged. All other source units are omitted. The four
   source theorems that follow them, M028.009–M028.012, are proposition
   targets in the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Statements`.
   No helper declaration or instance is added.

Exact-name searches of the Library found no existing declaration of either
name. This support module discharges no host class-formation, cup, transfer,
Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with no errors or warnings.
Declaration inspection of both definitions reported one universe parameter
and the axioms `propext`, `Classical.choice` and `Quot.sound`; for
`IsPrimeElement` it reported `statement_returns_prop: true`. Compilation and
inspection are separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
