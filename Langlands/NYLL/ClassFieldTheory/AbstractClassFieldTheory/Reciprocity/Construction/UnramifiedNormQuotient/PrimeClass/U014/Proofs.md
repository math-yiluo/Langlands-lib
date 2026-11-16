# The additive order of a prime class

This module proves the theorem
`Langlands.NYLL.ClassFormation.ValuationData.primeClass_addOrderOf`, the proof phase of
M058.014 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m058).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.ValuationData.primeClass_addOrderOfStatement` applied to the
theorem's parameters:

```lean
theorem primeClass_addOrderOf
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    primeClass_addOrderOfStatement v K L hLK hUnramified π hπ
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`, where `Langlands.NYLL.IntegralRepGroupType` (M002.001) is `Type 0`, since Mathlib's `Rep ℤ G` fixes the acting group to universe zero, and, in `namespace ValuationData`, `{D : DegreeData G} {A : Rep ℤ G}`. The theorem takes `v`, `K`, `L`, `hLK`, the finiteness instance, `hUnramified`, `π` and `hπ`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.PrimeClass.Statements`, the target is the proposition

```lean
addOrderOf (finiteNormClass A K.field L hLK π) =
  ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)
```

Here `K : FiniteAbstractField G` (M010.121) is a finite abstract field with closed subgroup `G_K = K.field.field`, `L` is a closed subgroup `G_L ≤ G_K` (`hLK`) of finite relative index, and `hUnramified` says that the abstract extension `L | K` (M010.044 `AbstractExtension.IsUnramified`) is unramified: `G_K ⊓ ker d ≤ G_L`, with `d = D.degree` the degree map of `D : DegreeData G`. `v : ValuationData D A` (M025.012) is a valuation datum, `v.valuationAt K` (M025.025) is the normalized valuation at `K` with values in `v.valueGroup ⊆ ℤ̂` (M025.013), and `hπ : v.IsPrimeElement K π` (M028.007) says `v.valuationAt K π = v.oneValue` (M028.005), so `π ∈ A^{G_K}` (`KummerTheory.ambientFixedAddSubgroup`, M023.001) is a prime element. `finiteNormClass A K.field L hLK π` (M039.006) is the class of `π` in the finite norm quotient `A^{G_K} / N_{L|K} A^{G_L}` (M039.002, with the norm subgroup `finiteNormSubgroup`, M039.001), and `FiniteAbstractFieldExtension.ofInclusion L K hLK` (M010.131) is the finite field extension `L | K`, whose degree `[L : K]` (M010.135) is the positive natural number `|G_K / G_L|`. The target says that the class of a prime element has additive order exactly `[L : K]`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.PrimeClass.Statements`, which defines the target and imports the finite norm quotient and its class map, prime elements, the abstract unramified predicate and `FiniteAbstractFieldExtension.ofInclusion`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`, the fixed-field inclusion `fixedFieldInclusion` (M028.001), the inclusion `A^{G_K} → A^{G_L}`, which does not change the underlying element of `A`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.Tower.Statements`, the statement module of M027.007, whose imports supply the relative norm `relativeNorm` (M024.009) with its value `relativeNormValue` (M024.005) and coset action `relativeCosetAction` (M024.001), the divided valuation `dividedAt` (M025.022), the norm composite `normCompositeAt` (M025.019) and the finite residue extension `toFiniteResidueAbstractExtension` (M010.140); its proposition is not used;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteTower.Definitions`, the finite tower structure `DegreeData.FiniteTower` (M010.105) and its finiteness instances (M010.106, M010.107);
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions`, the relative residue degree `FiniteAbstractFieldExtension.residueDegree` (M010.136), defined as the residue degree `FiniteAbstractExtension.residueDegree` (M010.086) of the underlying finite extension;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`, the published proof of M010.005 `le_baseField`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs`, the published proof of M010.036 `AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs`, the published proof of M010.027 `residueDegreeCardinal_eq_coe`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`, the published proof of M026.014 `relativeTowerQuotientFinite`;
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs`, the published proof of M009.005 `zHatMulNat_injective` (multiplication by a positive natural number on `ℤ̂` is injective);
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs`, the published proof of M009.017 `zHatMulNat_zHatDivide`.

The continuous additive reduction `zHatReduction n hn : ℤ̂ → ZMod n` (M008.018) comes through these imports. The module opens `KummerTheory`, `CyclicCohomology` and `scoped BigOperators`, as the M045.007 proof does; the source file opens the first two.

## Implemented proof

The main proof is the source proof. After `show` states the published proposition unfolded, it sets `E := ofInclusion L K hLK`, `n := [L : K]` and `g` the class of `π`, restates `hUnramified` as `hUn : E.IsUnramified D` by `change`, and records `0 < n`.

- Upper bound `hng : n • g = 0`: move `n` inside the class (M039.010, `rw [← …]`), reduce to `n • π` lying in the norm subgroup (M039.012), and give the witness `ι π`, with `ι` the fixed-field inclusion: `N_{L|K}(ι π) = n • π` is M028.003 at `E.toFiniteAbstractExtension`, restated by `change`.
- Divisibility `hdiv : m • g = 0 → n ∣ m`: from `m • g = 0` obtain `finiteNormClass (m • π) = 0` (`simpa [g, finiteNormClass_nsmul_aux]`), hence by M039.012 some `b ∈ A^{G_L}` with `N_{L|K} b = m • π`. The norm–valuation formula M027.007 at `b` gives `f_{L|K} • v_L(b) = v_K(N_{L|K} b)`; after `change` its multiplier is the relative residue degree `E.residueDegree D`, which unramifiedness turns into `n` (M010.138). The `calc` block `hval` then gives `n • v_L(b) = v_K(m • π) = m • v_K(π) = m • 1` in `ℤ̂` (`map_nsmul` for `v.valuationAt K`; `hπ` and M028.006 `(v.oneValue : ℤ̂) = 1`). Applying the reduction to `ZMod n` (`hredOne` by `rfl`, `simpa only [map_nsmul, hredOne]`) kills the left side, so `(m : ZMod n) = 0` and `n ∣ m` by `ZMod.natCast_eq_zero_iff`.
- Conclusion: `Nat.dvd_antisymm`, with `addOrderOf g ∣ n` from `hng` (`addOrderOf_dvd_iff_nsmul_eq_zero`) and `n ∣ addOrderOf g` from `hdiv` at `addOrderOf_nsmul_eq_zero g`.

The source prerequisites M039.010 `finiteNormClass_nsmul`, M039.012 `finiteNormClass_eq_zero_iff`, M028.003 `relativeNorm_fixedFieldInclusion`, M027.007 `ValuationData.normalizedValuation_tower`, M010.138 `FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` and M028.006 `ValuationData.oneValue_coe` have no published proofs in this Library. They are proved in this module as private theorems with an `_aux` suffix and with the source statements as explicit types:

- `finiteNormClass_nsmul_aux` is M039.010 with its source proof `map_nsmul (finiteNormClassHom A K L hLK) n a`; since the source lemma is `@[simp]` and the source writes `simpa [g]` in the divisibility step, the module writes `simpa [g, finiteNormClass_nsmul_aux]` there.
- `finiteNormClass_eq_zero_iff_aux` is M039.012 with its source proof: unfold `finiteNormClass`, `finiteNormClassHom` and `FiniteNormQuotient` and apply `QuotientAddGroup.eq_zero_iff`.
- `ValuationData.oneValue_coe_aux` is M028.006 with its source proof `rfl`.
- `relativeNorm_fixedFieldInclusion_aux` (M028.003) and `ValuationData.normalizedValuation_tower_aux` (M027.007), with the helpers `DegreeData.relativeResidueDegreeCardinal_eq_coe_aux` (M010.103), `DegreeData.residueDegree_mul_absoluteResidueDegree_aux` (M011.017), `ValuationData.residueDegree_nsmul_dividedAt_aux` (M025.023), `relativeCosetAction_towerProductEquiv_aux` (source-private M026.017) and `finiteTowerNormTransApplyAux_aux` (source-private M026.018), are the same Lean text as in Worker 745's accepted, not yet published candidate proof of M045.007 (artifact `a4f23504-029d-4999-8d0b-6848d2a77fa4`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteFieldUnitMaps.U007.Proofs`), which follows the shared drafts (revision 1) of Worker 5264 for Task `dd6e7eae-0db1-4832-bb64-e830afecdaf5` and Task `905dd316-beba-4d50-8384-657eb2f1e35f`. They follow the source proofs: M028.003 compares underlying elements, shows that every coset-action term of `ι a` is `a` (`a` is fixed by `G_K`), sums the constant and identifies the number of cosets with the degree through a local fact `hindex` proved by the source proof of M010.092; M027.007 multiplies by the base residue degree, uses the residue-degree tower law (M011.017, from the published M010.036 and M010.027 and the M010.103 helper) and `f • dividedAt = normCompositeAt` (M025.023), and concludes by transitivity of norms in the finite tower `L ≤ K ≤ baseField G` (M026.018, with M026.017 for the tower-product coset). As there, `extensionSubgroup K L h` is written as its abbreviation body `L.toSubgroup.subgroupOf K.toSubgroup`, and source rewrites with the `rfl` lemmas M024.002 `relativeCosetAction_mk`, M024.010 `relativeNorm_apply_coe` and M028.002 `fixedFieldInclusion_coe` are replaced by `change`, `show` and `rfl` steps.
- `residueDegree_eq_degree_of_isUnramified_aux` is M010.138 (and, through it, M010.100), `(E.residueDegree D : ℕ) = (E.degree : ℕ)` for an unramified `E : FiniteAbstractFieldExtension G`, by a route different from the source. The source proves M010.100 by the fundamental identity `[L:K] = f_{L|K} e_{L|K}` (M010.095, itself from the index identity M006.009) and `e_{L|K} = 1` (M010.096), and M010.138 by applying M010.100 to `E.toFiniteAbstractExtension`. The module instead works with relative indices directly: with `G_L ≤ G_K` (`E.below`) and unramifiedness `hUn : G_K ⊓ ker d ≤ G_L`, it proves `hsat : (G_L ⊔ ker d) ⊓ G_K = G_L` (an element of the left side is `y z` with `y ∈ G_L`, `z ∈ ker d` by `Subgroup.mem_sup_of_normal_right`; then `z = y⁻¹ (y z) ∈ G_K`, so `z ∈ G_L` by `hUn`). By `rfl`, the residue degree is `(d(G_L)).relIndex (d(G_K))` and the degree is `G_L.relIndex G_K`; the rewrites `← Subgroup.relIndex_comap`, `Subgroup.comap_map_eq` (`d⁻¹(d(G_L)) = G_L ⊔ ker d`), `← Subgroup.inf_relIndex_right` and `hsat` turn the first into the second.

The private theorems are not published copies of the unpublished results: they are private to this module and carry the `_aux` suffix.

The development check with `lean_check` in the approved environment compiled the
module over Library commit `72480b70c88adff84a438bd7029d64ee3977469c` with no errors
or warnings; the theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. This check does not establish independent semantic acceptance or
Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean`, lines 390–459](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean#L390-L459):
the docstring at lines 390–392 and the theorem at lines 393–459. It lies in `namespace ClassFormation` (line 23), after `universe u` (line 21), with `open KummerTheory` (line 25), `open CyclicCohomology` (line 27), its `noncomputable section` (line 31), in `section valuationQuotient` (line 152) with the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 155) and `{D : DegreeData G} {A : Rep ℤ G}` (line 156), inside `namespace ValuationData` (line 158). The source is:

```lean
/-- A prime class has exact additive order `[L : K]` in an unramified
norm quotient.  The lower bound is read after reduction in `ℤ̂/nℤ̂`; the
upper bound is the norm of the included prime. -/
theorem primeClass_addOrderOf
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    addOrderOf
      (finiteNormClass A K.field L hLK π) =
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) := by
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  let g : FiniteNormQuotient A K.field L hLK :=
    finiteNormClass A K.field L hLK π
  have hn : 0 < n := E.degree.property
  have hng : n • g = 0 := by
    change n • finiteNormClass A K.field L hLK π = 0
    rw [← finiteNormClass_nsmul]
    apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
    refine ⟨fixedFieldInclusion A K.field L hLK π, ?_⟩
    have hnorm :=
      relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension π
    change relativeNorm A K.field L hLK
        (fixedFieldInclusion A K.field L hLK π) = n • π at hnorm
    exact hnorm
  have hdiv : ∀ m : ℕ, m • g = 0 → n ∣ m := by
    intro m hm
    have hm' :
        finiteNormClass A K.field L hLK (m • π) = 0 := by
      simpa [g] using hm
    have hmNorm := (finiteNormClass_eq_zero_iff A K.field L hLK _).1 hm'
    obtain ⟨b, hb⟩ := hmNorm
    have htower := v.normalizedValuation_tower E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
    have hval :
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZHat) := by
      calc
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
            ((v.valuationAt K (relativeNorm A K.field L hLK b) :
              v.valueGroup) : ZHat) := htower
        _ = ((v.valuationAt K (m • π) : v.valueGroup) : ZHat) := by
          rw [hb]
        _ = m • ((v.valuationAt K π : v.valueGroup) : ZHat) := by
          exact congrArg Subtype.val (map_nsmul (v.valuationAt K) m π)
        _ = m • (1 : ZHat) := by rw [hπ, v.oneValue_coe]
    have hred := congrArg (fun z : ZHat => zHatReduction n hn z) hval
    have hredOne : zHatReduction n hn (1 : ZHat) = 1 := rfl
    have hred' :
        n • zHatReduction n hn
            ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZMod n) := by
      simpa only [map_nsmul, hredOne] using hred
    have hmzero : (m : ZMod n) = 0 := by
      have hmzero' : m • (1 : ZMod n) = 0 := by
        rw [← hred']
        simp [nsmul_eq_mul]
      simpa using hmzero'
    exact (ZMod.natCast_eq_zero_iff m n).1 hmzero
  apply Nat.dvd_antisymm
  · exact (addOrderOf_dvd_iff_nsmul_eq_zero).2 hng
  · exact hdiv (addOrderOf g) (addOrderOf_nsmul_eq_zero g)
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean`;
its SHA-256 is `66f9331ed7cc55c2f6726e4580486f0d4e1b6395d364313e77f5d8dbb17de1b6`.

The reproduced or replaced prerequisites are, in the same retained source tree:

- M039.010 `finiteNormClass_nsmul`: [`Reciprocity/Construction/FiniteNormQuotient.lean`, lines 124–133](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean#L124-L133), and M039.012 `finiteNormClass_eq_zero_iff`: [lines 147–157](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean#L147-L157) (SHA-256 `f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`);
- M028.006 `ValuationData.oneValue_coe`: [`Degree/PrimeElements.lean`, lines 115–119](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean#L115-L119), and M028.003 `relativeNorm_fixedFieldInclusion`: [lines 49–75](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean#L49-L75) (SHA-256 `9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`);
- M010.138 `FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified`: [`Degree/Fields.lean`, lines 1288–1294](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L1288-L1294), M010.100 `FiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified`: [lines 849–855](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L849-L855), M010.092 `FiniteAbstractExtension.extensionSubgroup_index_eq_degree`: [lines 782–785](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L782-L785), and M010.103 `FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe`: [lines 878–891](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L878-L891) (SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`);
- M027.007 `ValuationData.normalizedValuation_tower`: [`Degree/ValuationLaws.lean`, lines 164–202](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean#L164-L202) (SHA-256 `f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8`);
- M011.017 `FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`: [`Degree/Frobenius.lean`, lines 231–246](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean#L231-L246) (SHA-256 `d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`);
- M025.023 `ValuationData.residueDegree_nsmul_dividedAt`: [`Degree/Valuation.lean`, lines 255–263](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean#L255-L263) (SHA-256 `f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`);
- the source-private M026.017 `relativeCosetAction_towerProductEquiv` and M026.018 `finiteTowerNormTransApplyAux`: [`Degree/NormLaws.lean`, lines 349–431](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean#L349-L431) (SHA-256 `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`).

Modifications by Worker 745 on 16 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `primeClass_addOrderOfStatement v K L hLK hUnramified π hπ` as its type, and begin the proof with `show` stating it unfolded;
- replace `finiteNormClass_nsmul` by the private `finiteNormClass_nsmul_aux` (also added to the `simpa [g]` call, since the source relies on its `@[simp]` attribute), `finiteNormClass_eq_zero_iff` by `finiteNormClass_eq_zero_iff_aux`, `relativeNorm_fixedFieldInclusion` by `relativeNorm_fixedFieldInclusion_aux`, `v.normalizedValuation_tower E b` by `normalizedValuation_tower_aux v E b`, `E.residueDegree_eq_degree_of_isUnramified D hUn` by `residueDegree_eq_degree_of_isUnramified_aux E D hUn` and `v.oneValue_coe` by `oneValue_coe_aux`, proved as described above;
- omit the `@[simp]` attributes of the reproduced prerequisites, `universe u`, the `noncomputable section`, the section names and all other source declarations.

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
under Apache-2.0. The Lean file carries the dated modification record. The Lean text of
the M027.007 and M028.003 helpers was written by Worker 5264 (shared drafts for Tasks
`dd6e7eae-0db1-4832-bb64-e830afecdaf5` and `905dd316-beba-4d50-8384-657eb2f1e35f`);
Worker 745 assembled, rechecked and staged this module. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M058.014. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
