# The relative norm of a unit is a unit

This module proves the theorem
`Langlands.NYLL.ClassFormation.ValuationData.relativeNorm_mem_unitAddSubgroup`, the proof phase of
M045.010 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m045).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.ValuationData.relativeNorm_mem_unitAddSubgroupStatement` applied to the
theorem's parameters:

```lean
theorem relativeNorm_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) :
    relativeNorm_mem_unitAddSubgroupStatement v E u
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`, where `Langlands.NYLL.IntegralRepGroupType` (M002.001) is `Type 0`, since Mathlib's `Rep ℤ G` fixes the acting group to universe zero, and, in `namespace ValuationData`, `{D : DegreeData G} {A : Rep ℤ G}`. The theorem takes `v`, `E` and `u : v.unitAddSubgroup E.field`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps.Statements`, the target is the proposition

```lean
relativeNorm A E.base.field E.field.field E.below u.1 ∈
  v.unitAddSubgroup E.base
```

Here `E : FiniteAbstractFieldExtension G` (M010.130) is a finite extension `L | K` of bundled finite abstract fields, with closed subgroups `G_L = E.field.field ≤ E.base.field = G_K` (`E.below`); `v : ValuationData D A` (M025.012) is a valuation datum, `v.valuationAt K` (M025.025) is the normalized valuation at a finite abstract field `K`, an additive homomorphism from `A^{G_K}` (`KummerTheory.ambientFixedAddSubgroup`, M023.001) to the value group `v.valueGroup ⊆ ℤ̂` (M025.013), and `v.unitAddSubgroup K` (M028.008) is its kernel, the additive unit group `U_K`. `relativeNorm` (M024.009) is the relative norm `N_{L|K} : A^{G_L} → A^{G_K}`. The target says: if `u ∈ U_L`, then `N_{L|K} u ∈ U_K`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps.Statements`, which defines the target and imports the unit group, the normalized valuation, the relative norm and the finite field extensions;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Tower.Statements`, the statement module of M027.007, whose imports supply the divided valuation `dividedAt` (M025.022), the norm composite `normCompositeAt` (M025.019) and the finite residue extension `toFiniteResidueAbstractExtension` (M010.140); its proposition is not used;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions`, the finite tower structure `DegreeData.FiniteTower` (M010.105) and its finiteness instances (M010.106, M010.107);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`, the published proof of M010.005 `le_baseField`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs`, the published proof of M010.036 `AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs`, the published proof of M010.027 `residueDegreeCardinal_eq_coe`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`, the published proof of M026.014 `relativeTowerQuotientFinite`;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs`, the published proof of M009.005 `zHatMulNat_injective` (multiplication by a positive natural number on `ℤ̂` is injective);
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs`, the published proof of M009.017 `zHatMulNat_zHatDivide`.

The module opens `KummerTheory`, `CyclicCohomology` and `scoped BigOperators`, as the source does.

## Implemented proof

The main proof is the source proof. After `show` states the published proposition unfolded, it rewrites membership in `U_K` as `v.valuationAt E.base (N u) = 0` (M028.009), compares the underlying elements of `ℤ̂` (`Subtype.ext`), takes the norm–valuation formula (M027.007) at `u.1`, `f_{L|K} • v_L(u) = v_K(N_{L|K} u)`, restates it with `change` at `h`, and closes the goal by `simpa [hu] using h.symm`, where `hu : v.valuationAt E.field u.1 = 0` is the membership `u.2`: the left side of `h` becomes `f_{L|K} • 0 = 0`.

The two source prerequisites M028.009 `ValuationData.mem_unitAddSubgroup_iff` and M027.007 `ValuationData.normalizedValuation_tower` have unpublished proofs (routed to Tasks `e7bf198f-2d27-4442-a575-9740d4a68c96` and `dd6e7eae-0db1-4832-bb64-e830afecdaf5`). Their source proofs are reproduced in this module as private theorems with an `_aux` suffix and with the source statements as explicit types:

- `mem_unitAddSubgroup_iff_aux` is M028.009 with its source proof `Iff.rfl` (`U_K` is the kernel of `v.valuationAt K`).
- `normalizedValuation_tower_aux` is M027.007 with its source proof: multiply both sides by the base residue degree `f_K` (`zHatMulNat_injective`), write both sides with `dividedAt`, combine `f_K • f_{L|K} • _` by `smul_smul` and the residue-degree tower law `f_{L|K} f_K = f_L` (M011.017), rewrite `f • v.dividedAt` as norm composites (M025.023), and after a `change` to `v.toAddMonoidHom (normToBase …)` conclude by transitivity of norms in the finite tower `T` with `top := E.field.field`, `middle := E.base.field`, `base := baseField G` (`simpa [T, normToBase]`). Where the source writes `T.norm_trans_apply A a` (M026.019), the module applies `finiteTowerNormTransApplyAux_aux A T.base T.middle T.top T.top_le_middle T.middle_le_base a`, which is what the source proof of M026.019 does.
- The prerequisites of that proof whose proofs are unpublished are reproduced in the same way. `DegreeData.relativeResidueDegreeCardinal_eq_coe_aux` is the source proof of M010.103: a `change` to the cardinality of the quotient of the mapped subgroups, closed by `Nat.cast_card`. `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` is the source proof of M011.017: the published cardinal identity M010.036, rewritten with the M010.103 helper and the published M010.027 for base and field (stated as local equations `hbase`, `hfield`, since their types are published propositions), and `exact_mod_cast`. `residueDegree_nsmul_dividedAt_aux` is M025.023, `f_K • v.dividedAt K a = v.normCompositeAt K a`, as the source term `zHatMulNat_zHatDivide … (v.normCompositeAtInResidueImage K a)` (the source's `by exact` dropped). `finiteTowerNormTransApplyAux_aux` is the source-private M026.018, `N_{L/K}(N_{M/L} a) = N_{M/K} a` for closed subgroups `M ≤ L ≤ K` with finite relative quotients: it installs `Fintype` structures on the quotients, the one on `G_K ⧸ G_M` transported along `Subgroup.quotientTowerEquiv` and identified with `Fintype.ofFinite` by `Subsingleton.elim`, rewrites the outer sum termwise (`houter`), distributes over the inner sums (`map_sum`), turns the double sum into a sum over the product (`Fintype.sum_prod_type`) and reindexes along the tower equivalence (`Equiv.sum_comp`) after rewriting each term by `relativeCosetAction_towerProductEquiv_aux`, the source-private M026.017 (after `Quotient.inductionOn'`, a `change` to `A.ρ (q₀ * x) a = A.ρ q₀ (A.ρ x a)`, closed by `map_mul` and `rfl`).

These reproductions follow, with identical Lean text, the shared draft (revision 1) of Worker 5264 for Task `dd6e7eae-0db1-4832-bb64-e830afecdaf5`; `extensionSubgroup K L h` is written there as its abbreviation body `L.toSubgroup.subgroupOf K.toSubgroup`, and the source rewrites with the `rfl` lemmas M024.002 `relativeCosetAction_mk` and M024.010 `relativeNorm_apply_coe` are replaced by `rw [he]` with a `change`, two `rfl` steps in `houter`, and a `show` followed by `simp only [relativeNormValue]`. The private theorems are not published copies of the unpublished results: they are private to this module and carry the `_aux` suffix.

The development check with `lean_check` in the approved environment compiled the
module over Library commit `72480b70c88adff84a438bd7029d64ee3977469c` with no errors
or warnings. This check does not establish independent semantic acceptance or
Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean`, lines 217–235](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean#L217-L235):
the docstring at lines 217–219 and the theorem at lines 220–235. It lies in `namespace ClassFormation` (line 21), after `universe u v` (line 19), with `open KummerTheory` (line 23), `open CyclicCohomology` (line 24), its `noncomputable section` (line 28), `open CategoryTheory` (line 30), `open scoped BigOperators` (line 31) and the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 33), inside `namespace ValuationData` (line 60) with the variables `{D : DegreeData G} {A : Rep ℤ G}` (line 62). The source is:

```lean
/-- The norm of a unit through an arbitrary finite extension is a unit.
This is the valuation-theoretic step used when a finite Galois refinement
is pushed back down to the originally prescribed intermediate field. -/
theorem relativeNorm_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) :
    relativeNorm A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.base := by
  rw [v.mem_unitAddSubgroup_iff]
  apply Subtype.ext
  have h := v.normalizedValuation_tower E u.1
  let ER := E.toFiniteResidueAbstractExtension D
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field u.1 : v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ZHat) at h
  have hu : v.valuationAt E.field u.1 = 0 := u.2
  simpa [hu] using h.symm
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean`;
its SHA-256 is `7c304aaabeb8f4e08738e1d7e727db097444cf7d1cc011e1be6662cea5ba44fe`.

The reproduced prerequisites are, in the same retained source tree:

- M028.009 `ValuationData.mem_unitAddSubgroup_iff`: [`Degree/PrimeElements.lean`, lines 132–138](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean#L132-L138) (SHA-256 `9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`);
- M027.007 `ValuationData.normalizedValuation_tower`: [`Degree/ValuationLaws.lean`, lines 164–202](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean#L164-L202) (SHA-256 `f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8`);
- M010.103 `FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe`: [`Degree/Fields.lean`, lines 878–891](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L878-L891) (SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`);
- M011.017 `FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`: [`Degree/Frobenius.lean`, lines 231–246](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean#L231-L246) (SHA-256 `d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`);
- M025.023 `ValuationData.residueDegree_nsmul_dividedAt`: [`Degree/Valuation.lean`, lines 255–263](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean#L255-L263) (SHA-256 `f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`);
- the source-private M026.017 `relativeCosetAction_towerProductEquiv` and M026.018 `finiteTowerNormTransApplyAux`: [`Degree/NormLaws.lean`, lines 349–431](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean#L349-L431) (SHA-256 `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`).

Modifications by Worker 745 on 16 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `relativeNorm_mem_unitAddSubgroupStatement v E u` as its type, and begin the proof with `show` stating it unfolded;
- replace `v.mem_unitAddSubgroup_iff` by the private `mem_unitAddSubgroup_iff_aux` and `v.normalizedValuation_tower E u.1` by the private `normalizedValuation_tower_aux v E u.1`, reproducing the source proofs as described above (taken from the shared draft of Worker 5264 for Task `dd6e7eae-0db1-4832-bb64-e830afecdaf5`, with its modifications);
- omit the `@[simp]` attribute of M028.009, `open CategoryTheory`, `universe u v`, the `noncomputable section` and all other source declarations.

The main theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M045.010. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
