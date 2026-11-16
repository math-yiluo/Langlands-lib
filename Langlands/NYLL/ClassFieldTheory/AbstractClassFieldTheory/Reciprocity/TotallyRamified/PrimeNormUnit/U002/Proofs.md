# NYLL M083.002: a zero prime-norm class is the norm of a prime power times a unit

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.ValuationData.primeNormClass_eq_zero_exists_unit_norm_eqStatement`
by the theorem
`Langlands.NYLL.ClassFormation.ValuationData.primeNormClass_eq_zero_exists_unit_norm_eq`.
The theorem's type is exactly that proposition applied to its source
parameters,
`primeNormClass_eq_zero_exists_unit_norm_eqStatement v K L S hLK hSK hTot hSigmaResidue k piS piL hpiS hpiL hclass`.
Its only universe parameter is the one the statement itself carries; the
group `G` ranges over `IntegralRepGroupType`, as in the statement module.

Its direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.PrimeNormUnit.Statements`
(the target) and the published modules
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion`
(M010.131 `FiniteAbstractFieldExtension.ofInclusion`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions`
(the structure `DegreeData.FiniteTower`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions`
(`FiniteAbstractFieldExtension.residueDegree`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`
(`DegreeData.FiniteResidueAbstractExtension.residueDegree`),
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

The theorem has the section variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{D : DegreeData G} {A : Rep ℤ G}`, and then, in this order, the explicit
`v : ValuationData D A`, `K L S : FiniteAbstractField G`,
`hLK : L.field.toSubgroup ≤ K.field.toSubgroup`,
`hSK : S.field.toSubgroup ≤ K.field.toSubgroup`,
`hTot : (DegreeData.AbstractExtension.mk L.field K.field hLK).IsTotallyRamified D`,
the instance arguments `[hLKfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field hLK)]`
and `[hSKfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S.field hSK)]`,
`hSigmaResidue : ((DegreeData.FiniteAbstractExtension.ofInclusion S.field K.field hSK).residueDegree D : ℕ) = 1`,
`k : ℕ`, `piS : ambientFixedAddSubgroup A S.field`,
`piL : ambientFixedAddSubgroup A L.field`,
`hpiS : v.IsPrimeElement S piS`, `hpiL : v.IsPrimeElement L piL` and
`hclass : finiteNormClass A K.field L.field hLK (relativeNorm A K.field S.field hSK (k • piS)) = 0`.

So `L | K` is finite and totally ramified, `S | K` is finite with residue
degree one, `π_S` and `π_L` are prime elements, and the class of
`N_{S|K}(k • π_S)` in the finite norm quotient `A_K / N_{L|K} A_L` is zero.
Unfolding the target gives

`∃ w : v.unitAddSubgroup L, relativeNorm A K.field L.field hLK (k • piL + w.1) = relativeNorm A K.field S.field hSK (k • piS)`,

that is, `N_{S|K}(k • π_S) = N_{L|K}(k • π_L + u)` for a unit `u ∈ U_L`
(multiplicatively, `N_{S|K}(π_S^k) = N_{L|K}(π_L^k u)`).

## Implemented proof

The main proof is the source proof of M083.002, after a first `show`
unfolds the target. The numbered private theorems are listed below.

1. Item 7 turns `hclass` into membership of `N_{S|K}(k • π_S)` in the
   range of `relativeNorm A K.field L.field hLK`, and `obtain` gives
   `b ∈ A_L` with `hb : N_{L|K} b = N_{S|K}(k • π_S)`.
2. Two bundled extensions are formed: `EL`, the structure
   `FiniteAbstractFieldExtension` with field `L`, base `K`, inclusion `hLK`
   and finite quotient `hLKfinite`, and
   `ES := FiniteAbstractFieldExtension.ofInclusion S.field K hSK`.
3. `hvalB : v.valuationAt L b = k • v.oneValue` is proved by
   `Subtype.ext` in `ℤ̂`:
   - the tower formula (item 6) for `EL` at `b` and for `ES` at
     `k • π_S`, after `change` exposes the residue degrees
     `EL.residueDegree D` and `ES.residueDegree D`, gives
     `f_{L|K} • v_L(b) = v_K(N_{L|K} b)` and
     `f_{S|K} • v_S(k • π_S) = v_K(N_{S|K}(k • π_S))`;
   - `hTot` is, definitionally, `EL.IsTotallyRamified D`, so item 1 gives
     `f_{L|K} = 1`;
   - `f_{S|K} = 1` is derived from `hSigmaResidue`: with
     `ES₀ := DegreeData.FiniteAbstractExtension.ofInclusion S.field K.field hSK`,
     item 2 and `hSigmaResidue` give that the cardinal relative residue
     degree of `ES₀` is `1`; Mathlib's `Nat.cast_injective` into
     `Cardinal`, unfolding `FiniteAbstractFieldExtension.residueDegree`,
     a reverse rewrite with item 2 for `ES.toFiniteAbstractExtension`,
     and `simpa` with the definitions of `ES`, `ES₀`, both `ofInclusion`s
     and the two `toFiniteAbstractExtension`/`toAbstractExtension`
     projections close the goal;
   - after `one_nsmul`, the chain
     `v_L(b) = v_K(N_{L|K} b) = v_K(N_{S|K}(k • π_S)) = v_S(k • π_S) = k • v.oneValue`
     uses `hb`, then `map_nsmul` for `v.valuationAt S` and `hpiS`.
4. With `wL := b - k • π_L`, the valuation `v_L(wL)` is `0` by
   `map_sub`, `map_nsmul`, `hvalB`, `hpiL` and `sub_self`, so item 8 makes
   `wL` an element `w` of `v.unitAddSubgroup L`.
5. Finally `k • π_L + w = b` by `Subtype.ext`, `dsimp` and `abel`, so
   `N_{L|K}(k • π_L + w) = N_{L|K} b = N_{S|K}(k • π_S)` by `hb`.

The source proof uses results whose proofs are not yet published. The file
therefore proves the following private theorems, each by the source proof
of the named unit.

1. `DegreeData.FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified_aux`
   (M010.097): a totally ramified finite extension has `f_{L|K} = 1`, by
   `Subgroup.relIndex_eq_one`.
2. `DegreeData.FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux`
   (M010.103): the cardinal relative residue degree is the cast of the
   positive natural residue degree, by `Nat.cast_card`.
3. `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` (M011.017
   `FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`):
   `f_{L|K} · f_K = f_L`, from the published M010.036, item 2 and the
   published M010.027, by `exact_mod_cast`.
4. `relativeCosetAction_towerProductEquiv_aux` (source-private M026.017)
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
5. `ValuationData.residueDegree_nsmul_dividedAt_aux` (M025.023):
   `f_K • v.dividedAt K a = v.normCompositeAt K a`, by the published
   M009.017.
6. `ValuationData.normalizedValuation_tower_aux` (M027.007
   `ValuationData.normalizedValuation_tower`). Its type is the published
   proposition `normalizedValuation_towerStatement`, written out. Its proof
   applies the published M009.005 `zHatMulNat_injective` for `f_K`, uses
   item 3 to turn both sides into multiples by the absolute residue
   degrees, rewrites them with item 5 as `v(N_{L|k} a)` and
   `v(N_{K|k}(N_{L|K} a))`, and identifies these by item 4 for the finite
   tower `L ≤ K ≤ k` (built from `E.below`, `le_baseField`,
   `E.finiteQuotient` and `E.base.finite`).
7. `primeNormClass_finiteNormClass_eq_zero_iff_aux` (M039.012
   `finiteNormClass_eq_zero_iff`): a finite norm class is zero exactly when
   its representative lies in `finiteNormSubgroup`, by unfolding
   `finiteNormClass`, `finiteNormClassHom` and `FiniteNormQuotient` and
   Mathlib's `QuotientAddGroup.eq_zero_iff`.
8. `ValuationData.primeNormClass_mem_unitAddSubgroup_iff_aux` (M028.009
   `ValuationData.mem_unitAddSubgroup_iff`): `u ∈ v.unitAddSubgroup K` iff
   `v.valuationAt K u = 0`, by `Iff.rfl`.

No other auxiliary declaration, hypothesis, instance or `simp`
registration is introduced. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptations

- **Cited units.** The source's `finiteNormClass_eq_zero_iff`,
  `v.normalizedValuation_tower`,
  `EL.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified`,
  `ES₀.relativeResidueDegreeCardinal_eq_coe` (and its use for
  `ES.toFiniteAbstractExtension`) and `v.mem_unitAddSubgroup_iff` are
  replaced by the private items 7, 6, 1, 2 and 8, written with their full
  names and explicit arguments. These private names do not conflict with
  the adapted names of the units, which this module does not declare.
  Items 7 and 8 drop the source's `@[simp]` attribute, and item 7 writes
  the instance binder's `extensionSubgroup K L hLK` as its abbreviation
  body `L.toSubgroup.subgroupOf K.toSubgroup`, as in the published
  definitions.
- **`hTotEL`.** The source proves `EL.IsTotallyRamified D` by
  `simpa [EL, FiniteAbstractFieldExtension.IsTotallyRamified, FiniteAbstractFieldExtension.toFiniteAbstractExtension] using hTot`.
  With the published definitions this `simpa` leaves the finite-extension
  predicate unfolded only on one side, so the proof gives `hTot` directly,
  which has the required type by definitional unfolding.
- **Chain behind item 6.** Inside the private theorems, the source
  citations of M010.103, M011.017, M025.023 and M026.017–.019 are replaced
  by the private items above. Item 4 (M026.018) is applied directly to the
  components of the finite tower `T`, since the source proof of M026.019
  `DegreeData.FiniteTower.norm_trans_apply` is exactly that application.
  In item 3 the source rewrites with M010.027 become rewrites with local
  equations `hbase` and `hfield`, and a `change` precedes the rewrite with
  item 2.
- **Definitional lemmas.** The source rewrites with the unpublished `rfl`
  lemmas M010.093 `mapped_relIndex_eq_residueDegree` (item 1), M024.002
  `relativeCosetAction_mk` and M024.010 `relativeNorm_apply_coe` (item 4)
  are replaced by `change`, `show` and `rfl` steps with the same unfolded
  goals. In item 4 the abbreviation `extensionSubgroup K L hLK` is written
  as its body.
- The source theorem's conclusion is replaced by the published
  proposition applied to its parameters, which `show` unfolds first.

## Actual dependencies

- The published proposition
  `ValuationData.primeNormClass_eq_zero_exists_unit_norm_eqStatement`
  (unfolded only) in `Reciprocity/TotallyRamified/PrimeNormUnit/Statements`.
- The published definitions `FiniteAbstractField`,
  `FiniteAbstractFieldExtension` with its `ofInclusion`,
  `toFiniteAbstractExtension`, `IsTotallyRamified`, `residueDegree` and
  `toFiniteResidueAbstractExtension`, `DegreeData.AbstractExtension` with
  `IsTotallyRamified` and `relativeResidueDegreeCardinal`,
  `DegreeData.FiniteAbstractExtension` with its `ofInclusion`,
  `toAbstractExtension`, residue degree, `IsTotallyRamified` and
  `finiteQuotient`, `finiteNormSubgroup`, `FiniteNormQuotient`,
  `finiteNormClassHom`, `finiteNormClass`, `relativeCosetAction`,
  `relativeNormValue`, `relativeNorm`, `extensionSubgroup`, `baseField`,
  `ValuationData` with `normToBase`, `valueGroup`, `oneValue` and
  `normCompositeAt`, `ValuationData.valuationAt`, `dividedAt`,
  `normCompositeAtInResidueImage`, `IsPrimeElement` and
  `unitAddSubgroup`, reached through the import chain, and the directly
  imported definitions listed above.
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
- Mathlib's `QuotientAddGroup.eq_zero_iff`, `Subgroup.relIndex_eq_one`,
  `Nat.cast_card`, `Nat.cast_injective`, `Nat.cast_one`,
  `Quotient.inductionOn'`, `Quotient.out_eq'`, `Subtype.ext`,
  `Subsingleton.elim`, `Equiv.sum_comp`,
  `Subgroup.inclusion`, `Fintype.ofFinite`, `Fintype.ofEquiv`,
  `Fintype.sum_prod_type`, `Fintype.sum_congr`, `Finset.sum_congr`,
  `smul_smul`, `Nat.mul_comm`, `one_nsmul`, `map_nsmul`, `map_sub`,
  `sub_self`, `map_mul` and `map_sum`, and the `abel` tactic.

The unpublished M010.093, M010.097, M010.103, M011.017, M024.002,
M024.010, M025.023, M026.017–.019, M027.007, M028.009 and M039.012 are not
used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean:93–196`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean#L93-L196).
Lines 93–97 are the docstring, retained verbatim on the theorem, 98–122 the
signature and conclusion, and 122–196 the tactic proof retained above (the
partition's unit M083.002 spans lines 98–200, up to the next declaration).
The enclosing context is `namespace ClassFormation` (line 27),
`open KummerTheory` and `open CyclicCohomology` (lines 29 and 31),
`noncomputable section` (line 35), `open CategoryTheory` (line 37),
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 40), `namespace ValuationData` (line 89) and
`variable {D : DegreeData G} {A : Rep ℤ G}` (line 91). The source's
`noncomputable section` and `open CategoryTheory` are not needed by the
proof and are omitted.

The private theorems reproduce these source proofs (paths relative to
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/`):

| Private theorem | Source unit | Source lines |
| --- | --- | --- |
| `DegreeData.FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified_aux` | M010.097 | `Degree/Fields.lean` 822–828 |
| `DegreeData.FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux` | M010.103 | `Degree/Fields.lean` 878–891 |
| `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` | M011.017 | `Degree/Frobenius.lean` 231–246 |
| `relativeCosetAction_towerProductEquiv_aux` | M026.017 (private) | `Degree/NormLaws.lean` 349–368 |
| `finiteTowerNormTransApplyAux_aux` | M026.018 (private) | `Degree/NormLaws.lean` 370–431 |
| (direct application of the above) | M026.019 `DegreeData.FiniteTower.norm_trans_apply` | `Degree/NormLaws.lean` 437–446 |
| `ValuationData.residueDegree_nsmul_dividedAt_aux` | M025.023 | `Degree/Valuation.lean` 255–263 |
| `ValuationData.normalizedValuation_tower_aux` | M027.007 | `Degree/ValuationLaws.lean` 164–202 |
| `primeNormClass_finiteNormClass_eq_zero_iff_aux` | M039.012 | `Reciprocity/Construction/FiniteNormQuotient.lean` 147–157 |
| `ValuationData.primeNormClass_mem_unitAddSubgroup_iff_aux` | M028.009 | `Degree/PrimeElements.lean` 132–138 |

The whole-file SHA-256 values of the retained snapshot files, recomputed by
Worker 746 on 16 November 2026 UTC, are:

| File | SHA-256 |
| --- | --- |
| `Reciprocity/TotallyRamified.lean` | `0294844f85bffa1a3b4bc255c93c644b01f9e43dcd863a5e64718af4abcc0cc2` |
| `Reciprocity/Construction/FiniteNormQuotient.lean` | `f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7` |
| `Degree/Fields.lean` | `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e` |
| `Degree/Frobenius.lean` | `d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07` |
| `Degree/PrimeElements.lean` | `9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf` |
| `Degree/NormLaws.lean` | `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f` |
| `Degree/Valuation.lean` | `f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c` |
| `Degree/ValuationLaws.lean` | `f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8` |
| `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean` | `41d0b248e0b5cec84e6e20e7185a18746b8f79e2e9ba203ef7713c7c00a89115` |

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `ValuationData.primeNormClass_eq_zero_exists_unit_norm_eq` (M083.002) | Published `ValuationData.primeNormClass_eq_zero_exists_unit_norm_eqStatement` |
| Proof of `ValuationData.primeNormClass_eq_zero_exists_unit_norm_eq` | This theorem, same name, in `TotallyRamified/PrimeNormUnit/U002/Proofs` |
| `finiteNormClass_eq_zero_iff` (M039.012) | Private `primeNormClass_finiteNormClass_eq_zero_iff_aux` |
| `v.normalizedValuation_tower` (M027.007) | Private `ValuationData.normalizedValuation_tower_aux` |
| `residueDegree_eq_one_of_isTotallyRamified` (M010.097) | Private `DegreeData.FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified_aux` |
| `relativeResidueDegreeCardinal_eq_coe` (M010.103) | Private `DegreeData.FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux` |
| `v.mem_unitAddSubgroup_iff` (M028.009) | Private `ValuationData.primeNormClass_mem_unitAddSubgroup_iff_aux` |
| M011.017, M025.023, M026.017, M026.018 | Private `_aux` theorems of the table above |
| `T.norm_trans_apply` (M026.019) | Direct application of `finiteTowerNormTransApplyAux_aux` |
| `mapped_relIndex_eq_residueDegree`, `relativeCosetAction_mk`, `relativeNorm_apply_coe` (M010.093, M024.002, M024.010) | `change`, `show` and `rfl` |
| `FiniteAbstractFieldExtension.ofInclusion` (M010.131), `DegreeData.FiniteAbstractExtension.ofInclusion` | Published definitions of the same adapted names |
| `Subgroup.quotientTowerEquiv` (NYLL, `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean` 54–60) | Published `Langlands.NYLL.Subgroup.quotientTowerEquiv` |
| `le_baseField` (M010.005), `residueDegreeCardinal_eq_coe` (M010.027), `relativeResidueDegreeCardinal_mul_residueDegreeCardinal` (M010.036), `relativeTowerQuotientFinite` (M026.014), `zHatMulNat_injective` (M009.005), `zHatMulNat_zHatDivide` (M009.017) | Published theorems of the same adapted names |

The [public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m083)
places this proof at M083.002.

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
record. Worker 746 extracted the main proof and the private items 7 and 8
directly from the pinned original and the published statement. The private
items 1–6 are taken from Worker 5264's unreviewed shared draft, revision 1,
of Task 7030 (`dd6e7eae-0db1-4832-bb64-e830afecdaf5`, files
`Degree/ValuationLaws/Tower/U007/Proofs.lean` and
`Degree/PrimeElements/Prime/U012/Proofs.lean`), which reproduce the source
proofs listed above; Worker 746 checked them against the pinned source and
restated the tower theorem under a private name. There are no project
coauthors.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained,
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

This proof covers only M083.002. The published proofs of M010.097,
M010.103, M011.017, M025.023, M026.017–.019, M027.007, M028.009 and
M039.012, the rest of M083 and any reciprocity theorem are separate work.
