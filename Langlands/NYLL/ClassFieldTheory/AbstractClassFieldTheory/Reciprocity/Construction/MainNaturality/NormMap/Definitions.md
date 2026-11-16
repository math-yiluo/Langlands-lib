# NYLL norm map on finite norm quotients

The paired file adapts source unit M066.014 as the actual additive homomorphism
`Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityNormMap`. For a
representation `A` and closed subgroups with containments `L ≤ K`, `L′ ≤ K′`,
`K′ ≤ K` and `L′ ≤ L`, it sends the actual finite norm quotient for `L′ | K′`
to that for `L | K` by descending the relative norm from `K′` to `K`.
Finiteness of the quotients for `L | K`, `L′ | K′` and `K′ | K` is assumed.
No normality, continuity of the action, topological group or class-formation
hypothesis is added. This is data with its embedded proof, rather than a
proposition or a new proof of a separate theorem target.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`,
lines 422–474: documentation 422–423, definition telescope and result 424–437,
body 438–474. The complete source file has SHA-256
`0107befcff3ba066d7663120d9aa823ae72911cef7d3e72c5eeb5cb95f73a533`. Its section variables are on line 420, and its
noncomputable section and namespace are on lines 32 and 21.
The readable source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
the enclosing snapshot registration is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in the available project notes.

| Original declaration | Adapted or reused Library declaration |
| --- | --- |
| `ClassFormation.finiteReciprocityNaturalityNormMap` (M066.014) | `Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityNormMap` |
| Source-private `ClassFormation.finiteReciprocityNaturality_tower_finite` (M066.013) | `Langlands.NYLL.PortInternal.M066.d013` |
| `ClassFormation.FiniteIntermediateField.finite_extension_of_le` (M033.015) | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.finite_extension_of_le` |
| `ClassFormation.finiteNormClass_eq_zero_iff` (M039.012) | `Langlands.NYLL.ClassFormation.finiteNormClass_eq_zero_iff` |
| `ClassFormation.DegreeData.FiniteTower.norm_trans_apply` (M026.019) | `Langlands.NYLL.ClassFormation.DegreeData.FiniteTower.norm_trans_apply` |

Other referenced `ClassFormation` data (`FiniteNormQuotient`,
`finiteNormClassHom`, `relativeNorm`, `finiteNormQuotientLift` and
`DegreeData.FiniteTower`) and `KummerTheory.ambientFixedAddSubgroup` retain
their original suffixes under `Langlands.NYLL`. They are imported from the
published Library. In every occurrence, the source abbreviation
`CyclicCohomology.extensionSubgroup K L hLK` (M004.002, source
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54) is
expanded to its exact body `L.toSubgroup.subgroupOf K.toSubgroup`, with the
corresponding substitutions for `K′`, `L′` and the intermediate quotient.
The explicit containment witnesses remain as source parameters and in every
construction that uses them.

## Telescope, construction and modifications

The group parameter is the source's implicit `G : IntegralRepGroupType`,
with implicit group and topological-space instances. `IntegralRepGroupType`
chooses `Type 0`; this restriction comes from the source section, and does
not follow from `Rep` alone. The representation's module universe is arbitrary.
The remaining telescope, in order, is explicit `A : Rep ℤ G`, four closed
subgroups `K K′ L L′`, explicit containment witnesses `hLK`, `hL′K′`,
`hK′K`, `hL′L`, and instance binders `hLKfinite`, `hL′K′finite`, `hK′Kfinite`.
All binder kinds, names in the Lean file and their order are retained.

The construction installs the source's two local finite-quotient instances
`hL′Kfinite` and `hL′Lfinite`, using the published M066.013 and M033.015
proofs. It defines `f` as `finiteNormClassHom` composed with `relativeNorm`,
then applies the actual `finiteNormQuotientLift`. To show that `f` kills the
upper norm image, it retains the source's two concrete `FiniteTower`
structures `TLL′` and `TKK′`, with their original subgroup, containment and
finite-quotient fields. The published M039.012 criterion reduces vanishing
to membership in the lower norm image. The witness is the relative norm
from `L′` to `L`; the original calculation uses M026.019 twice, separated by
`congr 2` to identify the containment proofs. Every proof step and local
object from the source definition is retained.

The only mathematical name change beyond the namespace prefix is the
published internal name for the source-private M066.013 proof. The focused
imports replace the original broad `MainFiniteReciprocity` import. Unused
opens, the unused source `universe u`, and enclosing section labels are
omitted. The inaccurate source comment attributing the group universe
restriction to `Rep` is replaced with the explicit distinction above. No new
instances or auxiliary global declarations are introduced.

The original copyright, author and Apache-2.0 header is retained verbatim.
The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.
This support construction discharges no host class-formation, cup, transfer,
Tate or reciprocity theorem target.

## Development comparison

Development check `307f9528-22a1-41d3-a356-a6abf33a7e5e` compiled the entry
module and `NormMapSourceCheck` with zero errors or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.
The private `NormMapSourceCheck` module reconstructs the entire source
definition using the published prerequisites and the original subgroup
abbreviation, and checks equality of the complete unapplied constants by
`rfl`. This compares the entire telescope, result and construction without
adding assumptions. Independent semantic review and integration remain
required for publication.
