# NYLL M025: the norm to the base field and the valuation data

The paired Lean file adapts seven data declarations from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`.
The pinned source file has SHA-256
`f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found among the available project errata notes.

## Source correspondence

All adapted names have prefix `Langlands.NYLL.ClassFormation`; all original
names have prefix `ClassFormation`.

| Unit | Source declaration | Source lines (docstring; command) | Adapted declaration |
| --- | --- | --- | --- |
| M025.001 | `normToBase` (def) | 34; 35–40 | `normToBase` |
| M025.012 | `ValuationData` (structure) | 157–160; 161–175 | `ValuationData` |
| M025.013 | `ValuationData.valueGroup` (def) | 181; 182–183 | `ValuationData.valueGroup` |
| M025.014 | `ValuationData.canonicalQuotientMap` (def) | 185; 186–189 | `ValuationData.canonicalQuotientMap` |
| M025.015 | `ValuationData.cyclic_value_quotients` (def) | 191–192; 193–197 | `ValuationData.cyclic_value_quotients` |
| M025.016 | `ValuationData.valueModulo` (def) | 199; 200–203 | `ValuationData.valueModulo` |
| M025.019 | `ValuationData.normCompositeAt` (def) | 222; 223–225 | `ValuationData.normCompositeAt` |

The enclosing source context is `namespace ClassFormation` (line 19),
`open KummerTheory` (line 21), `open CyclicCohomology` (line 23),
`noncomputable section` (line 27), `universe u` (line 29), the comment and
group variables at lines 31–32, `namespace ValuationData` (line 177) and the
variables `{D : DegreeData G} {A : Rep ℤ G}` at line 179. All are retained.
All seven declaration docstrings and the four field docstrings are retained
verbatim.

The other names used by these declarations resolve to the following
published declarations:

| Original | Adapted | Unit |
| --- | --- | --- |
| `IntegralRepGroupType` | `Langlands.NYLL.IntegralRepGroupType` (`abbrev … := Type 0`) | — |
| `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField` | M010.003 |
| `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField` | M010.005 |
| `ClassFormation.DegreeData` | `Langlands.NYLL.ClassFormation.DegreeData` | M010.002 |
| `ClassFormation.FiniteAbstractField` | `Langlands.NYLL.ClassFormation.FiniteAbstractField` | M010.121 |
| anonymous instance `Finite (… ⧸ extensionSubgroup (baseField G) K.field …)` | `Langlands.NYLL.PortInternal.M010.d125` | M010.125 |
| `ClassFormation.FiniteAbstractField.residueDegree` | `Langlands.NYLL.ClassFormation.FiniteAbstractField.residueDegree` | M010.127 |
| `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` | M004.002 |
| `KummerTheory.ambientFixedAddSubgroup` | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` | M023.001 |
| `ClassFormation.relativeNorm` | `Langlands.NYLL.ClassFormation.relativeNorm` | M024.009 |
| `ClassFormation.ZHat` | `Langlands.NYLL.ClassFormation.ZHat` | M008.008 |
| `ClassFormation.nsmulWithin` | `Langlands.NYLL.ClassFormation.nsmulWithin` | M025.003 |
| `ClassFormation.nsmulImage` | `Langlands.NYLL.ClassFormation.nsmulImage` | M025.004 |
| `ClassFormation.canonicalValueQuotientMap` | `Langlands.NYLL.ClassFormation.canonicalValueQuotientMap` | M025.008 |

`ClosedSubgroup`, `Rep`, `AddSubgroup`, `AddMonoidHom.range`,
`AddMonoidHom.comp`, `Int.castRingHom`, `ZMod`, `AddEquiv.ofBijective` and
`QuotientAddGroup.mk'` are Mathlib's.

## Objects and complete telescopes

Every declaration begins with the section binders: implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, then `[Group G]` and
`[TopologicalSpace G]`. The acting group lies in `Type 0`; the carrier of
`A : Rep ℤ G` has an arbitrary universe, which is each declaration's single
(auto-bound) universe parameter. The declared `universe u` is not used by any
of these commands, as in the source. In the following, `A_K` denotes
`ambientFixedAddSubgroup A K`, the actual `K`-fixed additive subgroup of the
representation module, and `k` is the distinguished closed subgroup
`baseField G`.

**`normToBase`.** Explicit `(A : Rep ℤ G) (K : ClosedSubgroup G)`, then the
instance argument

```lean
[Finite ((baseField G).toSubgroup ⧸
  extensionSubgroup (baseField G) K (le_baseField K))]
```

with result `A_K →+ A_k`. The body is
`relativeNorm A (baseField G) K (le_baseField K)`, the published relative
norm N_{K|k} for the inclusion `K.toSubgroup ≤ (baseField G).toSubgroup`.
The published `le_baseField K` has type `le_baseFieldStatement K`, which
unfolds by definition to that inclusion. The published `extensionSubgroup` is
an `abbrev` for `K.toSubgroup.subgroupOf (baseField G).toSubgroup` that
ignores its inclusion argument. The instance binder is therefore exactly the
finiteness instance that `relativeNorm` requires for `K` inside `k`; elaboration
of the unchanged body confirms that it is found. There is no normality
hypothesis.

**`ValuationData`** (structure). Explicit parameters
`(D : DegreeData G) (A : Rep ℤ G)`, in `Type` of the carrier universe of `A`.
Its fields, in source order, are:

1. `toAddMonoidHom : A_k →+ ZHat`, the additive valuation on the base-field
   fixed module.
2. `integers_mem : ∀ m : ℤ, (Int.castRingHom ZHat) m ∈ toAddMonoidHom.range`:
   the image of every integer lies in the value group.
3. `canonical_value_quotient_bijective : ∀ (n : ℕ) (hn : 0 < n),
   Function.Bijective (canonicalValueQuotientMap toAddMonoidHom.range n hn)`:
   for every positive `n`, the published canonical map from the value group
   modulo `n`-th multiples to `ZMod n` is bijective.
4. `norm_range : ∀ K : FiniteAbstractField G,
   (toAddMonoidHom.comp (normToBase A K.field)).range =
   nsmulImage toAddMonoidHom.range (K.residueDegree D : ℕ)`: for every field
   finite over `k`, the values of norms from `A_K` are exactly the multiples of
   the value group by the absolute residue degree `f_K`. Here the finiteness
   instance for `normToBase A K.field` is the published
   `Langlands.NYLL.PortInternal.M010.d125`, and the `ℕ+`-valued residue degree
   is coerced to `ℕ`.

As the source docstring says, fields 2 and 3 are condition (i) of the
valuation-quotient axiom and field 4 is condition (ii). The constructor
`ValuationData.mk` takes `D` and `A` implicitly and the four fields explicitly.

The remaining definitions lie in namespace `ValuationData` with implicit
`{D : DegreeData G} {A : Rep ℤ G}` and an explicit `v : ValuationData D A`:

- `valueGroup v : AddSubgroup ZHat` is `v.toAddMonoidHom.range`, the value
  group `Z = v(A_k)`.
- `canonicalQuotientMap v (n : ℕ) (hn : 0 < n) :
  (v.valueGroup ⧸ nsmulWithin v.valueGroup n) →+ ZMod n` is
  `canonicalValueQuotientMap v.valueGroup n hn`.
- `cyclic_value_quotients v (n : ℕ) (hn : 0 < n) :
  (v.valueGroup ⧸ nsmulWithin v.valueGroup n) ≃+ ZMod n` is
  `AddEquiv.ofBijective (v.canonicalQuotientMap n hn)
  (v.canonical_value_quotient_bijective n hn)`. The equivalence is the
  canonical map itself, made invertible by the structure's bijectivity field;
  no other equivalence is chosen.
- `valueModulo v (n : ℕ) (hn : 0 < n) : v.valueGroup →+ ZMod n` is
  `(v.cyclic_value_quotients n hn).toAddMonoidHom.comp
  (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n))`, the quotient
  projection followed by that equivalence.
- `normCompositeAt v (K : FiniteAbstractField G) : A_{K.field} →+ ZHat` is
  `v.toAddMonoidHom.comp (normToBase A K.field)`, the composite
  `v ∘ N_{K|k}` before division by the residue degree.

## Modification record

Worker 110 made these changes:

1. Prefix the namespace `ClassFormation` with `Langlands.NYLL`; source
   references resolve to the published names in the table above.
2. Extract only the seven listed data commands. Their declaration kinds,
   binder order and kinds, types, structure fields, bodies and internal
   proof terms are unchanged.
3. Replace the source imports of `Degree.FrobeniusLift` and `Degree.Norm`
   (lines 7–8) by three focused published imports:
   `…Degree.Norm.RelativeNorm.Definitions` (`relativeNorm`, and transitively
   `ambientFixedAddSubgroup`, `IntegralRepGroupType`),
   `…Degree.Valuation.Definitions` (`nsmulWithin`, `nsmulImage`,
   `canonicalValueQuotientMap`, and transitively `ZHat`) and
   `…Degree.Fields.FiniteAbstractField.Residue.Definitions`
   (`FiniteAbstractField.residueDegree`, and transitively `DegreeData`,
   `baseField`, `le_baseField`, `extensionSubgroup`, `FiniteAbstractField` and
   the instance `PortInternal.M010.d125`). All three are prefixed
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory`.
4. Replace the source module docstring by a description of this module with
   a modification notice. Retain the source context listed above, including
   the opens, `noncomputable section` and the unused `universe u`.
5. Omit all other source units, in particular the theorems M025.005–006,
   M025.009–011 and M025.017 (`valueModulo_apply`), the targets M025.018 and
   M025.020 (in the paired `Statements` module), and all later
   normalized-valuation material. No helper declaration and no instance is
   added.

Exact-name searches of the Library found no existing declaration of these
seven names. This support module discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with no errors or warnings.
Inspection of `ValuationData` reported an inductive type with one universe
parameter, and the axioms `propext`, `Classical.choice` and `Quot.sound`.
A private probe assigned each unapplied constant, including
`ValuationData.mk`, to its full expected telescope at an arbitrary carrier
universe `u`, checked the type of every field projection, and checked each
definition body against the source body by reflexivity. Compilation and
inspection are separate from independent semantic acceptance and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
