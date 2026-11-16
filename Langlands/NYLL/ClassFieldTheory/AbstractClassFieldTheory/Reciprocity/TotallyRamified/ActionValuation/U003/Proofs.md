# NYLL M083.003: normalized valuation is invariant under the quotient action

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.ValuationData.valuationAt_extensionFixedRepresentation_actionStatement`
by the theorem
`Langlands.NYLL.ClassFormation.ValuationData.valuationAt_extensionFixedRepresentation_action`.
The theorem's type is exactly that proposition applied to its source
parameters,
`valuationAt_extensionFixedRepresentation_actionStatement v E hnormal q a`.
It has no universe parameters: the group `G` ranges over
`IntegralRepGroupType`, as in the statement module.

Its direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.ActionValuation.Statements`
(the target) and the published modules
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions`
(the structure `DegreeData.FiniteTower`),
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`
(M026.014 `relativeTowerQuotientFinite`),
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs`
(M009.005 `zHatMulNat_injective`) and
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs`
(M009.017 `zHatMulNat_zHatDivide`). The statement's Lean/Markdown pair and
its complete imported chain remain unchanged.

## Target and parameters

The theorem has, in this order, the explicit `v : ValuationData D A`,
`E : FiniteAbstractFieldExtension G`, the normality hypothesis
`hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal`,
a class `q : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field E.field.field E.below`
and a vector
`a : (extensionFixedRepresentation A E.base.field E.field.field E.below hnormal).V`;
the section variables are `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
and `{D : DegreeData G} {A : Rep ℤ G}`.

Here `E` is a finite extension `L | K` of finite abstract fields, with
`E.field` the field `L` and `E.base` the field `K`. The published
`extensionFixedRepresentation` is the representation of `G_K / G_L` on the
`G_L`-fixed vectors `A_L`, and `extensionFixedRepresentationEquiv` identifies
its carrier with `ambientFixedAddSubgroup A E.field.field`. Unfolding the
target gives

`v.valuationAt E.field (extensionFixedRepresentationEquiv … ((extensionFixedRepresentation …).ρ q a)) =
  v.valuationAt E.field (extensionFixedRepresentationEquiv … a)`,

that is, `v_L(q · a) = v_L(a)`.

## Implemented proof

The main proof is the source proof of M083.003. After `show` unfolds the
target, `Quotient.inductionOn'` reduces `q` to a class `QuotientGroup.mk r`
with `r : E.base.field.toSubgroup`. The local equation `heq` identifies
`extensionFixedRepresentationEquiv (ρ (mk r) a)` with
`normalExtensionAction A E.base.field E.field.field E.below hnormal r aL`,
where `aL` is the image of `a` in `A_L`; both have underlying vector
`A.ρ r.1 a.1`, so `Subtype.ext` and `rfl` prove it. After rewriting with
`heq`, the private copy of M032.018 described below closes the goal.

The source proof of M032.018 uses three results whose proofs are not yet
published. The file therefore proves the following private theorems, each
by the source proof of the named unit.

1. `relativeNorm_normalExtensionAction_aux` (M026.013
   `relativeNorm_normalExtensionAction`): for a finite normal extension the
   relative norm `N_{L|K}` is invariant under `normalExtensionAction`. The
   proof reindexes the coset sum by the bijection `Equiv.mulRight (mk k)` of
   the finite quotient and uses `map_mul` for `A.ρ`.
2. `relativeCosetAction_towerProductEquiv_aux` (source-private M026.017
   `relativeCosetAction_towerProductEquiv`): the coset action at the
   tower-product coset `(q, r)` is the action of a representative of `q` on
   the coset action at `r`.
3. `finiteTowerNormTransApplyAux_aux` (source-private M026.018
   `finiteTowerNormTransApplyAux`): for closed subgroups `M ≤ L ≤ K` with
   finite relative quotients, `N_{L|K} ∘ N_{M|L} = N_{M|K}`. The proof
   rewrites the total coset sum through the equivalence
   `Subgroup.quotientTowerEquiv` as a sum over the product of the two
   quotients, using item 2, `map_sum` and `Fintype.sum_prod_type`. In this
   namespace `Subgroup.quotientTowerEquiv` resolves to the published NYLL
   definition `Langlands.NYLL.Subgroup.quotientTowerEquiv` (module
   `Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower`), not to a
   Mathlib declaration. That definition composes Mathlib's
   `Subgroup.quotientEquivProdOfLE` with the NYLL
   `Langlands.NYLL.Subgroup.quotientSubgroupOfEquiv`.
4. `ValuationData.residueDegree_nsmul_dividedAt_aux` (M025.023
   `residueDegree_nsmul_dividedAt`): `f_K • v.dividedAt K a =
   v.normCompositeAt K a`, by the published M009.017
   `zHatMulNat_zHatDivide`.
5. `ValuationData.valuationAt_normalExtensionAction_aux` (M032.018
   `valuationAt_normalExtensionAction`): `v_L` is invariant under
   `normalExtensionAction`. Its type is the published proposition
   `valuationAt_normalExtensionActionStatement`, written out. The proof
   applies `Subtype.ext` and the published M009.005
   `zHatMulNat_injective` for the positive residue degree `f_L`, then
   computes with item 4 that `f_L • v_L(k · a)` and `f_L • v_L(a)` are
   `v(N_{L|k}(k · a))` and `v(N_{L|k}(a))`. These are equal because, for
   the finite tower `L ≤ K ≤ k` (built from `E.below`, `le_baseField`,
   `E.finiteQuotient` and `E.base.finite`), item 3 writes `N_{L|k}` as
   `N_{K|k} ∘ N_{L|K}` and item 1 removes the action inside `N_{L|K}`.

No other auxiliary declaration, hypothesis, instance or `simp`
registration is introduced. The development check reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

### Adaptations

- **M032.018.** The source's final step
  `exact v.valuationAt_normalExtensionAction E hnormal r aL` applies the
  private item 5 instead. Its private name does not conflict with the
  adapted name of M032.018, which this module does not declare.
- **M025.023, M026.013, M026.017, M026.018 and M026.019.** Inside item 5,
  the source cites `v.residueDegree_nsmul_dividedAt`,
  `relativeNorm_normalExtensionAction` and `T.norm_trans_apply`. The port
  cites items 4, 1 and 3; item 3 is applied directly to the components of
  the finite tower `T`, since the source proof of M026.019 is exactly that
  application (`exact finiteTowerNormTransApplyAux A T.base T.middle T.top
  T.top_le_middle T.middle_le_base a`). The source rewrite
  `rw [relativeNorm_normalExtensionAction …]` becomes `rw [hN]` with a local
  equation `hN` given by item 1.
- **Definitional lemmas.** The source rewrites with the unpublished `rfl`
  lemmas M024.002 `relativeCosetAction_mk`, M024.010
  `relativeNorm_apply_coe` and M026.012 `normalExtensionAction_coe` are
  replaced by `change`, `show` and `rfl` steps with the same unfolded
  goals.
- In items 1–3 the abbreviation `extensionSubgroup K L hLK` is written as
  its body `L.toSubgroup.subgroupOf K.toSubgroup`.
- The source theorem's conclusion is replaced by the published
  proposition applied to its parameters, which `show` unfolds first.

## Actual dependencies

- The published proposition
  `ValuationData.valuationAt_extensionFixedRepresentation_actionStatement`
  (unfolded only) in `Reciprocity/TotallyRamified/ActionValuation/Statements`.
- The published definitions `extensionFixedRepresentation` and
  `extensionSubgroup` (`GaloisCohomology/Cyclic/NormKernelVanishing/Extension/Definitions`),
  `extensionFixedRepresentationEquiv` (`Reciprocity/FieldRepresentation/FixedCarrier/Definitions`),
  `normalExtensionAction` (`Degree/NormLaws/Definitions`), `relativeCosetAction`
  and `relativeNormValue` (`Degree/Norm/Definitions`), `relativeNorm`
  (`Degree/Norm/RelativeNorm/Definitions`), `FiniteAbstractFieldExtension`
  (`Degree/Fields/FiniteAbstractField/Extension/Definitions`),
  `FiniteAbstractField.residueDegree` (`Degree/Fields/FiniteAbstractField/Residue/Definitions`),
  `baseField` (`Degree/Fields/Definitions`), `ValuationData` with
  `normToBase` (`Degree/Valuation/ValuationData/Definitions`) and
  `ValuationData.valuationAt`, `dividedAt`, `normCompositeAt` and
  `normCompositeAtInResidueImage` (`Degree/Valuation/ValuationData/Normalized/Definitions`),
  reached through the import chain.
- The published structure `DegreeData.FiniteTower`
  (`Degree/Fields/FiniteTower/Definitions`).
- The published NYLL equivalence `Langlands.NYLL.Subgroup.quotientTowerEquiv`
  (`Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower`, reached
  through `Degree/NormLaws/Definitions`), used in item 3 and written
  `Subgroup.quotientTowerEquiv` in the proof.
- The published theorems M010.005 `le_baseField` (`Degree/Fields/U005/Proofs`),
  M026.014 `relativeTowerQuotientFinite` (`Degree/NormLaws/U014/Proofs`),
  M009.005 `zHatMulNat_injective` (`GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U005/Proofs`)
  and M009.017 `zHatMulNat_zHatDivide` (`GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/Divide/U017/Proofs`).
- Mathlib's `Quotient.inductionOn'`, `Quotient.out_eq'`, `Subtype.ext`,
  `Equiv.mulRight`, `Equiv.sum_comp`, `Subgroup.inclusion`, `Fintype.ofFinite`, `Fintype.ofEquiv`,
  `Fintype.sum_prod_type`, `Fintype.sum_congr`, `Finset.sum_congr`,
  `map_mul` and `map_sum`.

The unpublished M024.002, M024.010, M025.023, M026.012, M026.013, M026.017,
M026.018, M026.019 and M032.018 are not used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean:198–235`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean#L198-L235).
Lines 198–200 are the docstring, 201–217 the signature and conclusion, and
218–235 the tactic proof retained above (the partition's unit M083.003 spans
lines 201–238, up to the next declaration). The enclosing context is
`namespace ClassFormation` (line 27), `open KummerTheory` and
`open CyclicCohomology` (lines 29 and 31), `noncomputable section`
(line 35), `open CategoryTheory` (line 37),
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 40), and `namespace ValuationData` with
`variable {D : DegreeData G} {A : Rep ℤ G}` (lines 89–91).

The private theorems reproduce these source proofs:

| Private theorem | Source unit | Source lines |
| --- | --- | --- |
| `relativeNorm_normalExtensionAction_aux` | M026.013 `relativeNorm_normalExtensionAction` | `Degree/NormLaws.lean` 284–313 |
| `relativeCosetAction_towerProductEquiv_aux` | M026.017 `relativeCosetAction_towerProductEquiv` (private) | `Degree/NormLaws.lean` 349–368 |
| `finiteTowerNormTransApplyAux_aux` | M026.018 `finiteTowerNormTransApplyAux` (private) | `Degree/NormLaws.lean` 370–431 |
| (direct application of the above) | M026.019 `DegreeData.FiniteTower.norm_trans_apply` | `Degree/NormLaws.lean` 437–446 |
| `ValuationData.residueDegree_nsmul_dividedAt_aux` | M025.023 `ValuationData.residueDegree_nsmul_dividedAt` | `Degree/Valuation.lean` 255–263 |
| `ValuationData.valuationAt_normalExtensionAction_aux` | M032.018 `ValuationData.valuationAt_normalExtensionAction` | `Reciprocity/Construction/UnitCohomologyAxiom.lean` 196–255 |

The whole-file SHA-256 values of the retained snapshot files, recomputed by
Worker 746 on 16 November 2026 UTC, are:

| File | SHA-256 |
| --- | --- |
| `Reciprocity/TotallyRamified.lean` | `0294844f85bffa1a3b4bc255c93c644b01f9e43dcd863a5e64718af4abcc0cc2` |
| `Reciprocity/Construction/UnitCohomologyAxiom.lean` | `05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5` |
| `Degree/NormLaws.lean` | `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f` |
| `Degree/Valuation.lean` | `f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c` |
| `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean` | `41d0b248e0b5cec84e6e20e7185a18746b8f79e2e9ba203ef7713c7c00a89115` |

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `ValuationData.valuationAt_extensionFixedRepresentation_action` (M083.003) | Published `ValuationData.valuationAt_extensionFixedRepresentation_actionStatement` |
| Proof `ValuationData.valuationAt_extensionFixedRepresentation_action` | This theorem of the same adapted name in `ActionValuation/U003/Proofs` |
| `v.valuationAt_normalExtensionAction` (M032.018) | Private `ValuationData.valuationAt_normalExtensionAction_aux` |
| `v.residueDegree_nsmul_dividedAt` (M025.023) | Private `ValuationData.residueDegree_nsmul_dividedAt_aux` |
| `relativeNorm_normalExtensionAction` (M026.013) | Private `relativeNorm_normalExtensionAction_aux` |
| `relativeCosetAction_towerProductEquiv` (M026.017) | Private `relativeCosetAction_towerProductEquiv_aux` |
| `finiteTowerNormTransApplyAux` (M026.018) | Private `finiteTowerNormTransApplyAux_aux` |
| `T.norm_trans_apply` (M026.019) | Direct application of `finiteTowerNormTransApplyAux_aux` |
| `relativeCosetAction_mk`, `relativeNorm_apply_coe`, `normalExtensionAction_coe` (M024.002, M024.010, M026.012) | `change`, `show` and `rfl` |
| `Subgroup.quotientTowerEquiv` (NYLL, `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean` 54–60) | Published `Langlands.NYLL.Subgroup.quotientTowerEquiv` |
| `relativeTowerQuotientFinite` (M026.014), `le_baseField` (M010.005), `zHatMulNat_injective` (M009.005), `zHatMulNat_zHatDivide` (M009.017) | Published theorems of the same adapted names |

The [public partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m083)
places this proof at M083.003.

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
record. Worker 746 extracted the main proof directly from the pinned
original and the published statement. The private theorems 1–4 and the
proof of the private theorem 5 are taken from Worker 5264's unreviewed
shared draft, revision 1, of Task 7030 (`dd6e7eae-0db1-4832-bb64-e830afecdaf5`,
file `Reciprocity/Construction/UnitCohomologyAxiom/ValuationAction/U018/Proofs.lean`),
which reproduces the source proofs listed above. Worker 746 checked them
against the pinned source and restated theorem 5 with its unfolded
proposition and a private name. There are no project coauthors.

The unchanged inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M083.003. The published proofs of M032.018,
M025.023 and M026.013–.019, the rest of M083 and any reciprocity theorem
are separate work.
