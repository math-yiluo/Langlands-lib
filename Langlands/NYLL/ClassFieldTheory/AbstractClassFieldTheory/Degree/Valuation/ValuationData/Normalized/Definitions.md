# NYLL M025.021, M025.022 and M025.025: the divided and the normalized valuation

This file adapts three definitions of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (docstring, declaration) | Original name after `ClassFormation.ValuationData.` | Adapted name |
| --- | --- | --- | --- |
| M025.021 | 233, 234–246 | `normCompositeAtInResidueImage` | `Langlands.NYLL.ClassFormation.ValuationData.normCompositeAtInResidueImage` |
| M025.022 | 248, 249–253 | `dividedAt` | `Langlands.NYLL.ClassFormation.ValuationData.dividedAt` |
| M025.025 | 286–287, 288–290 | `valuationAt` | `Langlands.NYLL.ClassFormation.ValuationData.valuationAt` |

## The objects

Every object is a published source definition. No replacement valuation,
norm, value group, residue degree or division map is introduced.

- `v : ValuationData D A` (M025.012) is the source's henselian valuation
  datum: an additive map `v.toAddMonoidHom` from the base-field fixed module
  `A_k` to `ZHat` (M008.008), with the fields `integers_mem`,
  `canonical_value_quotient_bijective` and `norm_range`. The field
  `norm_range K` says that the range of `v.toAddMonoidHom.comp (normToBase A K.field)`
  is `nsmulImage v.toAddMonoidHom.range f_K`.
- `v.valueGroup` (M025.013) is `v.toAddMonoidHom.range`, the value group `Z`,
  and `v.normCompositeAt K` (M025.019) is
  `v.toAddMonoidHom.comp (normToBase A K.field)`, the map `v ∘ N_{K|k}` on
  `A_K = ambientFixedAddSubgroup A K.field` (M023.001, namespace
  `Langlands.NYLL.KummerTheory`, hence the source open of `KummerTheory`). Both, with `ValuationData`, are
  published in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions`.
- `K : FiniteAbstractField G` (M010.121) is a field of finite degree over the
  distinguished base field, and `K.residueDegree D : ℕ+` (M010.127) is its
  absolute residue degree `f_K`.
- `nsmulImage Z n` (M025.004) is the image of `Z` under `z ↦ n • z`.
- `zHatMulNat n` (M009.002) is multiplication by `n` on `ZHat`, and
  `zHatDivide n hn` (M009.016) is the continuous inverse of
  `ZHat ≃ (zHatMulNat n).toAddMonoidHom.range` for `0 < n`, published in
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Definitions`.
- The published M009.018 theorem `zHatDivide_zHatMulNat n hn x` concludes the
  proposition `zHatDivide_zHatMulNatStatement n hn x`, which unfolds to
  `zHatDivide n hn ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x`. It is in
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U018.Proofs`.

## Telescopes

All three declarations have the source section's implicit binders
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}` (source
lines 32 and 179), followed by the explicit binders below. No hypothesis is
added. The group lies in `Type 0`, and the carrier universe of `A` is the
single universe parameter.

```lean
def normCompositeAtInResidueImage (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+
      (zHatMulNat (K.residueDegree D : ℕ)).toAddMonoidHom.range

def dividedAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ZHat

def valuationAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ v.valueGroup
```

## Constructions

`v.normCompositeAtInResidueImage K` (M025.021) sends `a ∈ A_K` to
`v(N_{K|k} a)`, regarded as an element of the subgroup `f_K ZHat`, the range
of `zHatMulNat f_K`. The membership proof is the source's. `v(N_{K|k} a)`
lies in the range of `v.normCompositeAt K`. By `norm_range` this range is
`nsmulImage v.valueGroup f_K`, so `v(N_{K|k} a) = f_K • z` for some `z` in
the value group, and `z` witnesses membership in the range of `zHatMulNat f_K`.
Additivity is inherited from `v.normCompositeAt K`.

`v.dividedAt K` (M025.022) is `zHatDivide f_K` composed with
`v.normCompositeAtInResidueImage K`. It is the map `a ↦ (1/f_K) v(N_{K|k} a)`
with values in `ZHat`. The body is the source's.

`v.valuationAt K` (M025.025) is the normalized valuation
`v_K = (1/f_K) v ∘ N_{K|k}`. It is `(v.dividedAt K).codRestrict v.valueGroup`,
whose underlying values are those of `v.dividedAt K`, with codomain the value
group `Z`. The membership argument is the source proof of M025.024
`dividedAt_mem_valueGroup`, inlined. Write `v(N_{K|k} a) = f_K • z` with
`z ∈ Z`, as above. The element `v.normCompositeAtInResidueImage K a` of
`f_K ZHat` is then `⟨zHatMulNat f_K z, ⟨z, rfl⟩⟩`. Dividing by `f_K` with
M009.018 gives `v.dividedAt K a = z`, which lies in `Z`.

## Modifications

Worker 5264 makes these modifications:

- Extract only M025.021, M025.022 and M025.025, with the source opens
  `KummerTheory` and `CyclicCohomology` (lines 21 and 23), the noncomputable
  section (line 27), the group-variable comment and variables (lines 31–32),
  `namespace ValuationData` (line 177) and its variables (line 179). Narrow the
  module documentation to these declarations. The source universe
  declaration `universe u` (line 29) is omitted because none of these
  declarations names `u`. The carrier universe of `A` remains a universe
  parameter, as in the source.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- In the membership proof of M025.021 (source lines 238–242), replace the
  source rewrite `rw [v.normCompositeAt_range K] at ha`, which uses the
  theorem M025.020, by a local hypothesis
  `hrange : (v.normCompositeAt K).range = nsmulImage v.valueGroup f_K`.
  It is proved by `v.norm_range K`, the source proof of M025.020 (source
  line 231), and the rewrite then uses `hrange`. The proposition and the rest
  of the proof are unchanged. This removes the dependence on the M025.020
  proof, which is routed separately (Task 6896).
- In the body of M025.025 (source line 290), replace the argument
  `fun a => v.dividedAt_mem_valueGroup K a`, which uses the theorem M025.024,
  by `fun a => by ...` with the source proof of M025.024 (source lines
  270–285). That proof uses `hrange` in the same way, and `zHatDivide_zHatMulNat`
  is the published M009.018 theorem, whose `Statement` proposition unfolds by
  definition to the source identity. The proposition proved for each `a` is
  `v.dividedAt K a ∈ v.valueGroup`, the statement of M025.024, so by proof
  irrelevance the map is the source's. M025.024 itself is a target in the
  sibling Statements module.
- Replace the source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift`
  and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm` by two
  published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions`
  contains `ValuationData`, `valueGroup` and `normCompositeAt`, and it
  imports `nsmulImage`, `FiniteAbstractField`, `residueDegree` and
  `ambientFixedAddSubgroup`;
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U018.Proofs`
  contains the M009.018 theorem and transitively imports `zHatMulNat` and
  `zHatDivide`.
- The declaration names, docstrings, telescopes, result types and the
  remaining construction bodies are unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The four source theorems between and after these definitions,
M025.023 `residueDegree_nsmul_dividedAt`, M025.024 `dividedAt_mem_valueGroup`,
M025.026 `valuationAt_coe` and M025.027 `normalizedValuation_surjective`, are
stated as proposition targets in the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Statements`.
These definitions discharge no host class-formation, cup, transfer, Tate or
reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Declaration inspection of `valuationAt` reported one universe parameter and
the axioms `propext`, `Classical.choice` and `Quot.sound`. Compilation is
separate from independent semantic acceptance and publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
