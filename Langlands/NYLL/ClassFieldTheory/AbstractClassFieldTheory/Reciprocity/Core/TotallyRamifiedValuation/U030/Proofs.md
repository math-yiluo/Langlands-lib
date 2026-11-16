# NYLL M075.030: the exponent endpoint of the totally ramified valuation argument

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.abstractReciprocity_totallyRamified_valuation_forces_exponent_zeroStatement`
by the theorem
`Langlands.NYLL.ClassFormation.abstractReciprocity_totallyRamified_valuation_forces_exponent_zero`.
The theorem's type is exactly that proposition applied to its source
parameters,
`abstractReciprocity_totallyRamified_valuation_forces_exponent_zeroStatement v E hTot k hk x hx`.
Its only universe parameter is the one the statement itself carries; the
group `G` ranges over `IntegralRepGroupType`, as in the statement module.

Its direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.TotallyRamifiedValuation.Statements`
(the target),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.ZHat.U028.Proofs`
(the published M075.028
`abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero`) and the published
modules
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

The theorem has, in this order, the implicit `{D : DegreeData G}` and
`{A : Rep ℤ G}`, and the explicit `v : ValuationData D A`,
`E : FiniteAbstractFieldExtension G`, `hTot : E.IsTotallyRamified D`,
`k : ℕ`, `hk : k < (E.degree : ℕ)`,
`x : ambientFixedAddSubgroup A E.base.field` and

`hx : ((v.valuationAt E.field (fixedFieldInclusion A E.base.field E.field.field E.below x) : v.valueGroup) : ZHat) = Int.castRingHom ZHat (k : ℤ)`;

the section variables are
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`.

Write `K = E.base` and `L = E.field`, so `L | K` is a finite totally
ramified extension and `x ∈ A_K`. The hypothesis `hx` says that `x`, viewed
in `A_L`, has normalized valuation the image of `k` in `ℤ̂`. Unfolding the
target gives the conclusion `k = 0`.

## Implemented proof

The main proof is the source proof of M075.030, after a first `show`
unfolds the target to `k = 0`:

```lean
  show k = 0
  have hn : 0 < (E.degree : ℕ) := E.degree.property
  apply abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero
    (E.degree : ℕ) k hn hk
    (((v.valuationAt E.base x : v.valueGroup) : ZHat))
  rw [← abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified_aux
    v E hTot]
  exact hx
```

The positivity `hn` is the property of the positive degree `E.degree : ℕ+`.
Applying the published M075.028 with `n = [L : K]`, the given `k`, `hn`,
`hk` and `z = v_K(x)` (whose type is the published proposition
`abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement`, which
unfolds to `k = 0`) leaves the goal `[L : K] • v_K(x) = k` in `ℤ̂`. Item 7
below rewrites `[L : K] • v_K(x)` back to `v_L(x)`, and `hx` closes the
goal.

The source proof cites M075.029, whose proof is not yet published. The file
therefore proves the following private theorems, each by the source proof
of the named unit.

1. `DegreeData.FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified_aux`
   (M010.097): a totally ramified finite extension has `f_{L|K} = 1`, by
   `Subgroup.relIndex_eq_one`.
2. `DegreeData.FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux`
   (M010.103): the cardinal relative residue degree is the cast of the
   positive natural residue degree, by `Nat.cast_card`.
3. `relativeNorm_fixedFieldInclusion_aux` (M028.003
   `relativeNorm_fixedFieldInclusion`): for a finite extension, the norm of
   an element already fixed over the base is its `[L : K]`-fold sum: every
   coset term of the norm sum is `a`, by `Quotient.inductionOn'` and the
   fixedness of `a`, and the number of terms is the index, which is
   `[L : K]` by `rfl` (the source lemma M010.092
   `extensionSubgroup_index_eq_degree`, here the local fact `hindex`).
4. `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` (M011.017
   `FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`):
   `f_{L|K} · f_K = f_L`, from the published M010.036, item 2 and the
   published M010.027, by `exact_mod_cast`.
5. `relativeCosetAction_towerProductEquiv_aux` (source-private M026.017)
   and `finiteTowerNormTransApplyAux_aux` (source-private M026.018): for
   closed subgroups `M ≤ L ≤ K` with finite relative quotients,
   `N_{L|K} ∘ N_{M|L} = N_{M|K}`, by rewriting the total coset sum through
   Mathlib's `Subgroup.quotientTowerEquiv` as a sum over the product of the
   two quotients.
6. `ValuationData.residueDegree_nsmul_dividedAt_aux` (M025.023,
   `f_K • v.dividedAt K a = v.normCompositeAt K a`, by the published
   M009.017) and `ValuationData.normalizedValuation_tower_aux` (M027.007
   `ValuationData.normalizedValuation_tower`). The type of the latter is
   the published proposition `normalizedValuation_towerStatement`, written
   out. Its proof applies the published M009.005 `zHatMulNat_injective`
   for `f_K`, uses item 4 to turn both sides into multiples by the
   absolute residue degrees, rewrites them with M025.023 as
   `v(N_{L|k} a)` and `v(N_{K|k}(N_{L|K} a))`, and identifies these by
   item 5 for the finite tower `L ≤ K ≤ k` (built from `E.below`,
   `le_baseField`, `E.finiteQuotient` and `E.base.finite`).
7. `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified_aux`
   (M075.029
   `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified`):
   `v_L(x) = [L : K] • v_K(x)` in `ℤ̂`. Its type is the source conclusion,
   that is, the published proposition
   `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamifiedStatement v E hTot x`
   written out, so that `rw` can use it. Its proof is the source proof:
   with `EF := E.toFiniteAbstractExtension` (and its finite quotient as a
   local instance), item 6 at `x` viewed in `A_L` gives, after `change`
   exposes the residue degree as `E.residueDegree D`,
   `f_{L|K} • v_L(x) = v_K(N_{L|K} x)`; item 1 and `one_nsmul` remove
   `f_{L|K}`; after `Subsingleton.elim` replaces `E.below` by `EF.below`
   and `change` rewrites in terms of `EF`, item 3 turns `N_{L|K} x` into
   `[L : K] • x`; a `Subtype.ext`/`rfl` step and `simpa` with the
   definition `FiniteAbstractFieldExtension.degree` give
   `v_L(x) = v_K([L : K] • x)`, and Mathlib's `map_nsmul` for
   `v.valuationAt E.base`, coerced by `congrArg Subtype.val`, finishes.

No other auxiliary declaration, hypothesis, instance or `simp`
registration is introduced. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptations

- **M075.029.** The source's
  `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified v E hTot`
  is replaced by the private item 7, a separately named private copy of
  the source theorem with its source proof (the same proof as the
  separately submitted M075.029 candidate of this task, whose published
  proof this module could import once it is in the Library). This private
  name does not conflict with the adapted name of M075.029, which this
  module does not declare.
- **M010.097, M027.007 and M028.003 inside item 7.** The source's
  `v.normalizedValuation_tower E _`,
  `EF.residueDegree_eq_one_of_isTotallyRamified D hTot` and
  `relativeNorm_fixedFieldInclusion A EF x` are replaced by the private
  items 6, 1 and 3, written with their full names.
- **Chain behind item 6.** Inside the private theorems, the source
  citations of M010.103, M011.017, M025.023 and M026.017–.019 are replaced
  by the private items above. Item 5 (M026.018) is applied directly to the
  components of the finite tower `T`, since the source proof of M026.019
  `DegreeData.FiniteTower.norm_trans_apply` is exactly that application.
  In item 4 the source rewrites with M010.027 become rewrites with local
  equations `hbase` and `hfield`, and a `change` precedes the rewrite with
  item 2.
- **Definitional lemmas.** The source rewrites with the unpublished `rfl`
  lemmas M010.093 `mapped_relIndex_eq_residueDegree` (item 1), M024.002
  `relativeCosetAction_mk` (items 3 and 5), M024.010
  `relativeNorm_apply_coe` (items 3 and 5) and M028.002
  `fixedFieldInclusion_coe` (item 3) are replaced by `change`, `show` and
  `rfl` steps with the same unfolded goals, and the rewrite with M010.092
  in item 3 by the local fact `hindex`, proved by `Subgroup.index` and
  `rfl`.
- In items 3 and 5 the abbreviation `extensionSubgroup K L hLK` is written
  as its body `L.toSubgroup.subgroupOf K.toSubgroup`.
- The source theorem's conclusion is replaced by the published
  proposition applied to its parameters, which `show` unfolds first. The
  source docstring is retained verbatim on the theorem.

## Actual dependencies

- The published proposition
  `abstractReciprocity_totallyRamified_valuation_forces_exponent_zeroStatement`
  (unfolded only) in `Reciprocity/Core/TotallyRamifiedValuation/Statements`.
- The published theorem M075.028
  `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero`
  (`Reciprocity/Core/ZHat/U028/Proofs`), with its published proposition
  `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement`.
- The published definitions `FiniteAbstractFieldExtension` with its
  `toFiniteAbstractExtension`, `IsTotallyRamified`, `degree`,
  `residueDegree` and `toFiniteResidueAbstractExtension`,
  `DegreeData.FiniteAbstractExtension` with its degree, residue degree,
  `IsTotallyRamified` and `finiteQuotient`, `fixedFieldInclusion`,
  `relativeCosetAction`, `relativeNormValue`, `relativeNorm`,
  `extensionSubgroup`, `baseField`, `ZHat`, `ValuationData` with
  `normToBase`, `valueGroup` and `normCompositeAt`,
  `ValuationData.valuationAt`, `dividedAt` and
  `normCompositeAtInResidueImage`, reached through the import chain, and
  the directly imported definitions listed above.
- The published theorems M010.005 `le_baseField`, M010.027
  `FiniteResidueAbstractField.residueDegreeCardinal_eq_coe`, M010.036
  `AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal`,
  M026.014 `relativeTowerQuotientFinite`, M009.005 `zHatMulNat_injective`
  and M009.017 `zHatMulNat_zHatDivide`.
- Mathlib's `ℕ+` (whose defining property gives `hn` as
  `E.degree.property`), `Int.castRingHom`,
  `Subgroup.relIndex_eq_one`, `Subgroup.index`, `Nat.cast_card`,
  `Nat.card_eq_fintype_card`, `Finset.sum_const`, `Finset.card_univ`,
  `Quotient.inductionOn'`, `Quotient.out_eq'`, `Subtype.ext`,
  `Subsingleton.elim`, `Equiv.sum_comp`, `Subgroup.quotientTowerEquiv`,
  `Subgroup.inclusion`, `Fintype.ofFinite`, `Fintype.ofEquiv`,
  `Fintype.sum_prod_type`, `Fintype.sum_congr`, `Finset.sum_congr`,
  `smul_smul`, `one_nsmul`, `map_nsmul`, `map_mul` and `map_sum`.

The unpublished M010.092, M010.093, M010.097, M010.103, M011.017,
M024.002, M024.010, M025.023, M026.017–.019, M027.007, M028.002, M028.003
and the proof of M075.029 are not used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean:1245–1266`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean#L1245-L1266).
Lines 1245–1247 are the docstring, retained verbatim on the theorem,
1248–1259 the signature and conclusion, and 1259–1266 the tactic proof
retained above (the partition's unit M075.030 spans lines 1248 to the end
of the file, line 1270, whose last three lines close the sections and the
namespace). The enclosing context is `namespace ClassFormation`
(line 24), `open KummerTheory`, `open CyclicCohomology` and
`open CategoryTheory` (lines 26, 28 and 34), and the nested
`noncomputable section`s opened at lines 32 and 451, the inner one with
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 454); the theorem binds `{D : DegreeData G}` and `{A : Rep ℤ G}`
itself.

The private theorems reproduce these source proofs (paths relative to
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/`):

| Private theorem | Source unit | Source lines |
| --- | --- | --- |
| `DegreeData.FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified_aux` | M010.097 | `Degree/Fields.lean` 822–828 |
| `DegreeData.FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe_aux` | M010.103 | `Degree/Fields.lean` 878–891 |
| `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` | M011.017 | `Degree/Frobenius.lean` 231–246 |
| `relativeNorm_fixedFieldInclusion_aux` | M028.003 | `Degree/PrimeElements.lean` 49–75 |
| `relativeCosetAction_towerProductEquiv_aux` | M026.017 (private) | `Degree/NormLaws.lean` 349–368 |
| `finiteTowerNormTransApplyAux_aux` | M026.018 (private) | `Degree/NormLaws.lean` 370–431 |
| (direct application of the above) | M026.019 `DegreeData.FiniteTower.norm_trans_apply` | `Degree/NormLaws.lean` 437–446 |
| `ValuationData.residueDegree_nsmul_dividedAt_aux` | M025.023 | `Degree/Valuation.lean` 255–263 |
| `ValuationData.normalizedValuation_tower_aux` | M027.007 | `Degree/ValuationLaws.lean` 164–202 |
| `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified_aux` | M075.029 | `Reciprocity/Core.lean` 1178–1243 |

The whole-file SHA-256 values of the retained snapshot files, recomputed by
Worker 746 on 16 November 2026 UTC, are:

| File | SHA-256 |
| --- | --- |
| `Reciprocity/Core.lean` | `0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb` |
| `Degree/Fields.lean` | `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e` |
| `Degree/Frobenius.lean` | `d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07` |
| `Degree/PrimeElements.lean` | `9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf` |
| `Degree/NormLaws.lean` | `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f` |
| `Degree/Valuation.lean` | `f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c` |
| `Degree/ValuationLaws.lean` | `f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8` |

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `abstractReciprocity_totallyRamified_valuation_forces_exponent_zero` (M075.030) | Published `abstractReciprocity_totallyRamified_valuation_forces_exponent_zeroStatement` |
| Proof of `abstractReciprocity_totallyRamified_valuation_forces_exponent_zero` | This theorem, same name, in `TotallyRamifiedValuation/U030/Proofs` |
| `abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero` (M075.028) | Published theorem of the same adapted name |
| `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified` (M075.029) | Private `abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified_aux` |
| `v.normalizedValuation_tower` (M027.007) | Private `ValuationData.normalizedValuation_tower_aux` |
| `EF.residueDegree_eq_one_of_isTotallyRamified` (M010.097) | Private `DegreeData.FiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified_aux` |
| `relativeNorm_fixedFieldInclusion` (M028.003) | Private `relativeNorm_fixedFieldInclusion_aux` |
| M010.103, M011.017, M025.023, M026.017, M026.018 | Private `_aux` theorems of the table above |
| `T.norm_trans_apply` (M026.019) | Direct application of `finiteTowerNormTransApplyAux_aux` |
| `extensionSubgroup_index_eq_degree` (M010.092) | Local fact `hindex` |
| `mapped_relIndex_eq_residueDegree`, `relativeCosetAction_mk`, `relativeNorm_apply_coe`, `fixedFieldInclusion_coe` (M010.093, M024.002, M024.010, M028.002) | `change`, `show` and `rfl` |
| `le_baseField` (M010.005), `residueDegreeCardinal_eq_coe` (M010.027), `relativeResidueDegreeCardinal_mul_residueDegreeCardinal` (M010.036), `relativeTowerQuotientFinite` (M026.014), `zHatMulNat_injective` (M009.005), `zHatMulNat_zHatDivide` (M009.017) | Published theorems of the same adapted names |

The [public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m075)
places this proof at M075.030.

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
record. Worker 746 extracted the main proof and item 7 directly from the
pinned original and the published statements. Items 1–6 are taken from
Worker 5264's unreviewed shared draft, revision 1, of Task 7030
(`dd6e7eae-0db1-4832-bb64-e830afecdaf5`, files
`Degree/ValuationLaws/Tower/U007/Proofs.lean`,
`Degree/PrimeElements/Prime/U010/Proofs.lean` and
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

This proof covers only M075.030. The published proofs of M075.029,
M010.097, M010.103, M011.017, M025.023, M026.017–.019, M027.007 and
M028.003, the rest of M075 and any reciprocity theorem are separate work.
