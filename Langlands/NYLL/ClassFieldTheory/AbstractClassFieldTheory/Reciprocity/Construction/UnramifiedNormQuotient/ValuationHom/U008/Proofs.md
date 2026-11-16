# NYLL M058.008: finite norms lie in the kernel of the unramified valuation map

This module proves the published Library proposition
`Langlands.NYLL.PortInternal.M058.d008Statement` by the theorem
`Langlands.NYLL.PortInternal.M058.d008`. The theorem's type is exactly that
proposition applied to its source parameters,
`d008Statement v K L hLK hUnramified`. Its only universe parameter is the
one the statement itself carries; the group `G` ranges over
`IntegralRepGroupType`, as in the statement module.

The target ports the private source theorem
`ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker`. The
published `Langlands.NYLL.PortInternal.M058.d007` ports the private source
definition `ValuationData.unramifiedValuationHom`, so the source's
`v.unramifiedValuationHom K L hLK` reads `d007 v K L hLK`.

Its direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.ValuationHom.Statements`
(the target) and the published modules
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions`
(the structure `DegreeData.FiniteTower`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions`
(`FiniteAbstractFieldExtension.residueDegree`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`
(`DegreeData.FiniteResidueAbstractExtension.residueDegree`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U006.Definitions`
(`kernelCosetEquivSaturation`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`
(M010.005 `le_baseField`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs`
(M010.036 `AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs`
(M010.027 `FiniteResidueAbstractField.residueDegreeCardinal_eq_coe`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`
(M026.014 `relativeTowerQuotientFinite`),
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs`
(M009.005 `zHatMulNat_injective`) and
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs`
(M009.017 `zHatMulNat_zHatDivide`). The statement's Lean/Markdown pair and
its complete imported chain remain unchanged.

## Target and parameters

The theorem has, in this order, the explicit `v : ValuationData D A`,
`K : FiniteAbstractField G`, `L : ClosedSubgroup G` and
`hLK : L.toSubgroup ≤ K.field.toSubgroup`, the instance argument
`[Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]` and the
unramifiedness hypothesis
`hUnramified : (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D`;
the section variables are `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
and `{D : DegreeData G} {A : Rep ℤ G}`.

Here `L ≤ K` is a finite extension of the finite abstract field `K` by the
closed subgroup `L`, and `d007 v K L hLK : A_K →+ ZMod [L : K]` is the
normalized valuation `v_K` followed by the published reduction
`v.valueModulo [L : K]` of the value group modulo the degree. Unfolding the
target gives

`finiteNormSubgroup A K.field L hLK ≤ (d007 v K L hLK).ker`,

that is, `v_K(N_{L|K} a) ≡ 0 mod [L : K]` for every `a ∈ A_L`.

## Implemented proof

The main proof is the source proof of M058.008. After `show` unfolds the
target, `rintro _ ⟨a, rfl⟩` takes a norm `N_{L|K} a` from the range
`finiteNormSubgroup A K.field L hLK = (relativeNorm A K.field L hLK).range`.
With `E := FiniteAbstractFieldExtension.ofInclusion L K hLK` and
`n := [L : K]`, the hypothesis is restated as `E.IsUnramified D` by
`change`. The tower formula (item 10 below) at `a` gives
`f_{L|K} • v_L(a) = v_K(N_{L|K} a)` in `ℤ̂`; `change` exposes the residue
degree as `E.residueDegree D`, and the unramified residue degree identity
(item 4) rewrites it to `n`. By `Subtype.ext`,
`v_K(N_{L|K} a) = n • v_L(a)` in the value group. After `change` writes the
kernel condition as `v.valueModulo n _ (v_K(N_{L|K} a)) = 0` and rewriting
with this equation, item 8 with the witness `v_L(a)` closes the goal.

The source proof uses one source-private helper and results whose proofs
are not yet published. The file therefore proves the following private
theorems, each by the source proof of the named unit.

1. `relIndex_eq_map_relIndex_mul_inf_ker_relIndex_aux` (M006.009
   `relIndex_eq_map_relIndex_mul_inf_ker_relIndex`): for a group
   homomorphism `d` and subgroups `L ≤ K`, `[K : L]` is the relative index
   of the images times that of the kernel intersections. The source proofs
   of M006.008 `map_relIndex_eq_saturation_relIndex` and M006.007
   `relIndex_saturation_eq_inf_ker_relIndex` are the local facts `hmap` and
   `hsat` (the latter by the published `kernelCosetEquivSaturation`).
2. `DegreeData.FiniteAbstractExtension.degree_eq_residueDegree_mul_ramificationIndex_aux`
   (M010.095): `[L : K] = f_{L|K} · e_{L|K}`, by item 1 for the degree map.
3. `DegreeData.FiniteAbstractExtension.ramificationIndex_eq_one_of_isUnramified_aux`
   (M010.096): an unramified finite extension has `e_{L|K} = 1`, by
   `Subgroup.relIndex_eq_one`.
4. `DegreeData.FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified_aux`
   (M010.100): an unramified finite extension has `f_{L|K} = [L : K]`, by
   items 2 and 3.
5. `FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified_aux`
   (M010.138): the same for a finite extension of finite abstract fields, as
   item 4 applied to `E.toFiniteAbstractExtension`.
6. `DegreeData.FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux`
   (M010.103): the cardinal relative residue degree is the cast of the
   positive natural residue degree, by `Nat.cast_card`.
7. `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` (M011.017
   `FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`):
   `f_{L|K} · f_K = f_L`, from the published M010.036, item 6 and the
   published M010.027, by `exact_mod_cast`.
8. `ValuationData.valueModulo_eq_zero_iff_aux` (source-private M058.006
   `ValuationData.valueModulo_eq_zero_iff`): `v.valueModulo n hn z = 0` iff
   `z = n • w` for some `w` in the value group, using injectivity of the
   published `v.cyclic_value_quotients n hn` and
   `QuotientAddGroup.eq_zero_iff`.
9. `relativeCosetAction_towerProductEquiv_aux` (source-private M026.017)
   and `finiteTowerNormTransApplyAux_aux` (source-private M026.018): for
   closed subgroups `M ≤ L ≤ K` with finite relative quotients,
   `N_{L|K} ∘ N_{M|L} = N_{M|K}`, by rewriting the total coset sum through
   `Subgroup.quotientTowerEquiv` as a sum over the product of the two
   quotients. In this namespace `Subgroup.quotientTowerEquiv` resolves to
   the published NYLL definition `Langlands.NYLL.Subgroup.quotientTowerEquiv`
   (module `Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower`), not
   to a Mathlib declaration. That definition composes Mathlib's
   `Subgroup.quotientEquivProdOfLE` with the NYLL
   `Langlands.NYLL.Subgroup.quotientSubgroupOfEquiv`.
10. `ValuationData.residueDegree_nsmul_dividedAt_aux` (M025.023,
    `f_K • v.dividedAt K a = v.normCompositeAt K a`, by the published
    M009.017) and `ValuationData.normalizedValuation_tower_aux` (M027.007
    `ValuationData.normalizedValuation_tower`). The type of the latter is
    the published proposition `normalizedValuation_towerStatement`, written
    out. Its proof applies the published M009.005 `zHatMulNat_injective`
    for `f_K`, uses item 7 to turn both sides into multiples by the
    absolute residue degrees, rewrites them with M025.023 as
    `v(N_{L|k} a)` and `v(N_{K|k}(N_{L|K} a))`, and identifies these by
    item 9 for the finite tower `L ≤ K ≤ k` (built from `E.below`,
    `le_baseField`, `E.finiteQuotient` and `E.base.finite`).

No other auxiliary declaration, hypothesis, instance or `simp`
registration is introduced. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptations

- **M058.006, M010.138 and M027.007.** The source's
  `v.normalizedValuation_tower E a`,
  `E.residueDegree_eq_degree_of_isUnramified D hUn` and
  `v.valueModulo_eq_zero_iff n E.degree.property _` are replaced by the
  private items 10, 5 and 8, written with their full names. These private
  names do not conflict with the adapted names of the units, which this
  module does not declare.
- **Chain behind items 5 and 10.** Inside the private theorems, the source
  citations of M006.007–.009, M010.095, M010.096, M010.100, M010.103,
  M011.017, M025.023 and M026.017–.019 are replaced by the private items
  above. Item 9 (M026.018) is applied directly to the components of the
  finite tower `T`, since the source proof of M026.019
  `DegreeData.FiniteTower.norm_trans_apply` is exactly that application.
  In item 7 the source rewrites with M010.027 become rewrites with local
  equations `hbase` and `hfield`, and a `change` precedes the rewrite with
  item 6.
- **Definitional lemmas.** The source rewrites with the unpublished `rfl`
  lemmas M010.091 `relIndex_eq_degree`, M010.093
  `mapped_relIndex_eq_residueDegree`, M010.094
  `inertia_relIndex_eq_ramificationIndex`, M024.002
  `relativeCosetAction_mk` and M024.010 `relativeNorm_apply_coe` are
  replaced by `change`, `show` and `rfl` steps with the same unfolded
  goals.
- In item 9 the abbreviation `extensionSubgroup K L hLK` is written as its
  body `L.toSubgroup.subgroupOf K.toSubgroup`.
- The source theorem's conclusion is replaced by the published
  proposition applied to its parameters, which `show` unfolds first, and
  `v.unramifiedValuationHom K L hLK` by its published port `d007 v K L hLK`.

## Actual dependencies

- The published proposition `PortInternal.M058.d008Statement` (unfolded
  only) and definition `PortInternal.M058.d007` in
  `Reciprocity/Construction/UnramifiedNormQuotient/ValuationHom/`.
- The published definitions `finiteNormSubgroup`
  (`Reciprocity/Construction/FiniteNormQuotient/Definitions`),
  `FiniteAbstractFieldExtension.ofInclusion`
  (`Degree/Fields/FiniteAbstractField/Extension/OfInclusion`),
  `FiniteAbstractFieldExtension`, `DegreeData.FiniteAbstractExtension` and
  their degrees, residue degrees, ramification indices and `IsUnramified`
  predicates, `relativeCosetAction`, `relativeNormValue`, `relativeNorm`,
  `extensionSubgroup`, `baseField`, `ValuationData` with `normToBase`,
  `valueGroup`, `cyclic_value_quotients`, `valueModulo` and
  `normCompositeAt`, `nsmulWithin`, `ValuationData.valuationAt`,
  `dividedAt` and `normCompositeAtInResidueImage`, reached through the
  import chain, and the directly imported definitions listed above.
- The published NYLL equivalence `Langlands.NYLL.Subgroup.quotientTowerEquiv`
  (`Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower`, reached
  through `Degree/NormLaws/Definitions`), used in
  `finiteTowerNormTransApplyAux_aux` and written
  `Subgroup.quotientTowerEquiv` in the proof.
- The published theorems M010.005 `le_baseField`, M010.027
  `FiniteResidueAbstractField.residueDegreeCardinal_eq_coe`, M010.036
  `AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal`,
  M026.014 `relativeTowerQuotientFinite`, M009.005 `zHatMulNat_injective`
  and M009.017 `zHatMulNat_zHatDivide`.
- Mathlib's `Subgroup.relIndex_comap`, `Subgroup.comap_map_eq`,
  `Subgroup.inf_relIndex_right`, `Subgroup.relIndex_mul_relIndex`,
  `Subgroup.relIndex_eq_one`, `Nat.card_congr`, `Nat.cast_card`,
  `QuotientAddGroup.eq_zero_iff`, `Quotient.inductionOn'`,
  `Quotient.out_eq'`, `Subtype.ext`, `Equiv.sum_comp`,
  `Subgroup.inclusion`, `Fintype.ofFinite`,
  `Fintype.ofEquiv`, `Fintype.sum_prod_type`, `Fintype.sum_congr`,
  `Finset.sum_congr`, `smul_smul`, `map_mul` and `map_sum`.

The unpublished M006.007–.009, M010.091, M010.093–.096, M010.100,
M010.103, M010.138, M011.017, M024.002, M024.010, M025.023,
M026.017–.019, M027.007 and the source-private M058.006 are not used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:195–221`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean#L195-L221).
Lines 195–203 are the signature and conclusion (the source theorem has no
docstring) and 204–221 the tactic proof retained above (the partition's
unit M058.008 spans lines 195–223, up to the next declaration). The
enclosing context is `namespace ClassFormation` (line 23),
`open KummerTheory` and `open CyclicCohomology` (lines 25 and 27),
`noncomputable section` (line 31), `section valuationQuotient` (line 152),
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`variable {D : DegreeData G} {A : Rep ℤ G}` (lines 155–156), and
`namespace ValuationData` (line 158).

The private theorems reproduce these source proofs (paths relative to
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/`):

| Private theorem | Source unit | Source lines |
| --- | --- | --- |
| `relIndex_eq_map_relIndex_mul_inf_ker_relIndex_aux` | M006.009, with M006.008 and M006.007 as `hmap` and `hsat` | `Degree/Indices.lean` 109–121, 100–107, 91–98 |
| `DegreeData.FiniteAbstractExtension.degree_eq_residueDegree_mul_ramificationIndex_aux` | M010.095 | `Degree/Fields.lean` 803–811 |
| `DegreeData.FiniteAbstractExtension.ramificationIndex_eq_one_of_isUnramified_aux` | M010.096 | `Degree/Fields.lean` 813–820 |
| `DegreeData.FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified_aux` | M010.100 | `Degree/Fields.lean` 849–855 |
| `FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified_aux` | M010.138 | `Degree/Fields.lean` 1288–1294 |
| `DegreeData.FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux` | M010.103 | `Degree/Fields.lean` 878–891 |
| `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` | M011.017 | `Degree/Frobenius.lean` 231–246 |
| `ValuationData.valueModulo_eq_zero_iff_aux` | M058.006 (private) | `Reciprocity/Construction/UnramifiedNormQuotient.lean` 160–181 |
| `relativeCosetAction_towerProductEquiv_aux` | M026.017 (private) | `Degree/NormLaws.lean` 349–368 |
| `finiteTowerNormTransApplyAux_aux` | M026.018 (private) | `Degree/NormLaws.lean` 370–431 |
| (direct application of the above) | M026.019 `DegreeData.FiniteTower.norm_trans_apply` | `Degree/NormLaws.lean` 437–446 |
| `ValuationData.residueDegree_nsmul_dividedAt_aux` | M025.023 | `Degree/Valuation.lean` 255–263 |
| `ValuationData.normalizedValuation_tower_aux` | M027.007 | `Degree/ValuationLaws.lean` 164–202 |

The whole-file SHA-256 values of the retained snapshot files, recomputed by
Worker 746 on 16 November 2026 UTC, are:

| File | SHA-256 |
| --- | --- |
| `Reciprocity/Construction/UnramifiedNormQuotient.lean` | `66f9331ed7cc55c2f6726e4580486f0d4e1b6395d364313e77f5d8dbb17de1b6` |
| `Degree/Indices.lean` | `da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71` |
| `Degree/Fields.lean` | `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e` |
| `Degree/Frobenius.lean` | `d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07` |
| `Degree/NormLaws.lean` | `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f` |
| `Degree/Valuation.lean` | `f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c` |
| `Degree/ValuationLaws.lean` | `f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8` |
| `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean` | `41d0b248e0b5cec84e6e20e7185a18746b8f79e2e9ba203ef7713c7c00a89115` |

| Original in `ClassFormation` | Adapted in `Langlands.NYLL` |
| --- | --- |
| Asserted type of the private `ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker` (M058.008) | Published `PortInternal.M058.d008Statement` |
| Proof of `ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker` | This theorem `PortInternal.M058.d008` in `ValuationHom/U008/Proofs` |
| Private `v.unramifiedValuationHom K L hLK` (M058.007) | Published `PortInternal.M058.d007 v K L hLK` |
| Private `v.valueModulo_eq_zero_iff` (M058.006) | Private `ClassFormation.ValuationData.valueModulo_eq_zero_iff_aux` |
| `v.normalizedValuation_tower` (M027.007) | Private `ClassFormation.ValuationData.normalizedValuation_tower_aux` |
| `E.residueDegree_eq_degree_of_isUnramified` (M010.138) | Private `ClassFormation.FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified_aux` |
| M010.100, M010.096, M010.095, M010.103, M011.017, M025.023, M026.017, M026.018, M006.009 | Private `_aux` theorems of the table above |
| `T.norm_trans_apply` (M026.019) | Direct application of `finiteTowerNormTransApplyAux_aux` |
| `relIndex_eq_degree`, `mapped_relIndex_eq_residueDegree`, `inertia_relIndex_eq_ramificationIndex`, `relativeCosetAction_mk`, `relativeNorm_apply_coe` (M010.091, M010.093, M010.094, M024.002, M024.010) | `change`, `show` and `rfl` |
| `Subgroup.quotientTowerEquiv` (NYLL, `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean` 54–60) | Published `Langlands.NYLL.Subgroup.quotientTowerEquiv` |
| `le_baseField` (M010.005), `residueDegreeCardinal_eq_coe` (M010.027), `relativeResidueDegreeCardinal_mul_residueDegreeCardinal` (M010.036), `relativeTowerQuotientFinite` (M026.014), `zHatMulNat_injective` (M009.005), `zHatMulNat_zHatDivide` (M009.017) | Published theorems of the same adapted names |

The [public partition](../../../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m058)
places this proof at M058.008.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including "Naganori Yamaguchi
(assisted by OpenAI Codex)", followed by Worker 746's dated modification
record. Worker 746 extracted the main proof and item 8 directly from the
pinned original and the published statement. The other private theorems
are taken from Worker 5264's unreviewed shared draft, revision 1, of Task
7030 (`dd6e7eae-0db1-4832-bb64-e830afecdaf5`, files
`Degree/ValuationLaws/Tower/U007/Proofs.lean` and
`Degree/PrimeElements/Prime/U010/Proofs.lean`), which reproduce the source
proofs listed above. Worker 746 checked them against the pinned source,
added item 5 from its source term proof, and restated the tower theorem
under a private name. There are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M058.008. The published proofs of M006.007–.009,
M010.095, M010.096, M010.100, M010.103, M010.138, M011.017, M025.023, M026.017–.019 and M027.007, the rest of
M058 and any reciprocity theorem are separate work.
