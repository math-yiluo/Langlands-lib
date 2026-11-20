import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicDeterminantLine
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLevi
import Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.PointDecomposition
import Langlands.LocalField.ResidueNormalization
import Langlands.Representation.Aubert.General.DynamicUnipotentHaarDeterminantProof

/-! # The minimal parabolic modulus as a normalized adjoint determinant -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise WithZero

namespace Langlands.HarishChandraSchwartz

open Langlands.HarmonicAnalysis
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Scalar
variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Forward additive Haar scaling by a field unit is its residue-normalized absolute value. -/
theorem distribHaarChar_eq_residueNormalizedAbsoluteValue (a : Fˣ) :
    ((distribHaarChar F a : ℝ≥0) : ℝ) = LocalField.residueNormalizedAbsoluteValue F (a : F) := by
  let v := FML.normalizedMultiplicativeValuation F
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hE : v.IsEquiv (ValuativeRel.valuation F) :=
    Valuation.isEquiv_map_self_of_strictMono e.toMulEquiv.toMonoidWithZeroHom e.strictMono
  let π : Fˣ := Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)
  have hπ0 : v (π : F) ≠ 0 := v.ne_zero_iff.mpr π.ne_zero
  have hπord := LocalField.ord_uniformizer F
  rw [FML.ord_of_ne_zero F (LocalField.uniformizer_ne_zero F)] at hπord
  have hπval : v (π : F) = WithZero.exp (-1) := by
    have h : -(WithZero.log (v (π : F))) = 1 := WithTop.coe_injective hπord
    rw [← WithZero.exp_log hπ0]
    congr 1
    omega
  have hπ : GeneralLinear.Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) π := by
    refine ⟨?_, fun x hx => ⟨-WithZero.log (v x), ?_⟩⟩
    · rw [hE.lt_one_iff_lt_one.symm, hπval, WithZero.exp_lt_one_iff]
      norm_num
    · rw [← map_zpow₀, hE.eq_iff.symm, map_zpow₀, hπval, ← WithZero.exp_zsmul,
        smul_neg, smul_eq_mul, mul_one, neg_neg, WithZero.exp_log (v.ne_zero_iff.mpr hx)]
  let abv := LocalField.residueNormalizedAbsoluteValue F
  have hunit (x : F) (hx : ValuativeRel.valuation F x = 1) : abv x = 1 := by
    change (WithZeroMulInt.toNNReal _ (v x) : ℝ) = 1
    rw [hE.eq_one_iff_eq_one.mpr hx, map_one, NNReal.coe_one]
  borelize F
  let haar : Measure F := addHaar
  have h := Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement F
    (LocalField.residueCardinality F) rfl abv π hπ
    (LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F))
    hunit haar a⁻¹
  have hmap : DomMulAct.mk a • haar = (Shahidi.absUnits abv a : ℝ≥0) • haar := by
    change haar.map (fun x => (a⁻¹ : Fˣ) • x) = _
    simpa only [Units.smul_def, smul_eq_mul, map_inv, Units.val_inv_eq_inv_val, inv_inv] using h
  have hchar : distribHaarChar F a = (Shahidi.absUnits abv a : ℝ≥0) := by
    have := GeneralLocalField.haarMeasure_regular F haar
    let s : Set F := FML.ringOfIntegers F
    have hs0 : haar s ≠ 0 :=
      ((GeneralLocalField.isOpen_integer F).measure_pos haar ⟨0, Subring.zero_mem _⟩).ne'
    have hstop : haar s ≠ ⊤ := (GeneralLocalField.isCompact_integer F).measure_ne_top
    apply distribHaarChar_eq_of_measure_smul_eq_mul hs0 hstop
    simpa only [Measure.domSMul_apply, Equiv.symm_apply_apply, coe_nnreal_smul_apply]
      using congrArg (fun ν : Measure F => ν s) hmap
  exact congrArg (fun r : ℝ≥0 => (r : ℝ)) hchar

end Scalar

private theorem closedNormalizerCharacter_congr
    {H : Type*} [Group H] [TopologicalSpace H] [LocallyCompactSpace H] [IsTopologicalGroup H]
    {U V : Subgroup H} (hUV : U = V)
    (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H)) {g g' : H}
    (hg : g ∈ Subgroup.normalizer (U : Set H))
    (hg' : g' ∈ Subgroup.normalizer (V : Set H)) (h : g = g') :
    HaarModulus.closedNormalizerCharacter U hU ⟨g, hg⟩ =
      HaarModulus.closedNormalizerCharacter V hV ⟨g', hg'⟩ := by
  subst V g'
  rfl

section Determinant

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

local instance : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

/-- The minimal modulus is the absolute value of the determinant on the actual minimal
radical Lie algebra, in any represented models of the two dynamic subgroups. -/
theorem rationalMinimalModulus_eq_abs_adjointDeterminant
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {P U : GroupScheme (Spec (CommRingCat.of F))} {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iU)
    [IsAffine P.X.left] [IsAffineHom U.X.hom] {d : ℕ} (cU : Lie.FiniteCoordinates U d)
    (p : standardParabolicPoints i ν ∅) :
    (((rationalMinimalModulus i ν p : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      LocalField.residueNormalizedAbsoluteValue F
        (Dynamic.adjointDeterminantPointValue iP (Dynamic.adjointDeterminantCharacter hP hU cU)
          (p : rationalPoints G)) := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hPeq : standardParabolicPoints i ν ∅ = RationalPoint.parabolic χ := by
    change (standardParabolic i ν ∅).carrier _ = (Dynamic.parabolic χ).carrier _
    rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
  have hUeq : standardUnipotentPoints i ν ∅ = RationalPoint.unipotent χ := by
    change (standardUnipotent i ν ∅).carrier _ = (Dynamic.unipotent χ).carrier _
    rw [standardUnipotent_empty_eq_dynamic i ν hG hi]
  obtain ⟨⟨m, n⟩, ⟨hm, hn, hp⟩, -⟩ :=
    RationalPoint.existsUnique_levi_mul_unipotent χ (hPeq.le p.2)
  let mP : standardParabolicPoints i ν ∅ :=
    ⟨m, hPeq.ge (RationalPoint.levi_le_parabolic χ hm)⟩
  let nP : standardParabolicPoints i ν ∅ :=
    ⟨n, hPeq.ge (RationalPoint.unipotent_le_parabolic χ hn)⟩
  have hp' : p = mP * nP := Subtype.ext hp
  have hnmod := rationalMinimalModulus_eq_one_of_mem_standardUnipotent hG hi hν nP (hUeq.ge hn)
  let cG := Lie.finiteCoordinates G
  have : Mono iU.hom.hom := hU.1
  let v := Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ F)
  have hv : v ≠ 0 := Dynamic.adjointExteriorCoordinates_ne_zero
    cG cU (CommAlgCat.of _ F) (Field.toIsField F)
  have hev := Dynamic.isEigenvectorOn_adjointExteriorCoordinates hP hU cG cU
  have hnDet := MatrixRepresentation.eigenvalue_eq_one_of_mem_unipotent F χ _ hv le_rfl hev hn
  have hmul := MatrixRepresentation.eigenvalue_mul hv hev
    (RationalPoint.levi_le_parabolic χ hm) (RationalPoint.unipotent_le_parabolic χ hn)
  rw [hp', map_mul, hnmod, mul_one]
  change (((rationalMinimalModulus i ν mP : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
    LocalField.residueNormalizedAbsoluteValue F
      (Dynamic.adjointDeterminantPointValue iP (Dynamic.adjointDeterminantCharacter hP hU cU) (m * n))
  rw [hmul, hnDet, mul_one]
  let iZ := Dynamic.Affine.centralizerHom χ
  have hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have : IsAffineHom (Dynamic.Affine.centralizerScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ).isAffineHom
  have : IsAffine (Dynamic.Affine.centralizerScheme χ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerScheme χ).X.hom
  have hmZ : m ∈ (Dynamic.centralizer χ).rationalPoints := hm
  rw [SubgroupFunctor.rationalPoints_eq_range hZ] at hmZ
  obtain ⟨z, hz⟩ := hmZ
  have hzN : z ≫ iZ.hom.hom ∈ Subgroup.normalizer (RationalPoint.unipotent χ : Set (rationalPoints G)) := by
    change rationalPoints.map iZ z ∈ _
    rw [hz]
    exact RationalPoint.levi_le_normalizer_unipotent χ hm
  have hUc : IsClosed (RationalPoint.unipotent χ : Set (rationalPoints G)) := by
    rw [← hUeq]
    exact isClosed_standardUnipotentPoints i ν ∅
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hHaar := Aubert.General.RationalPointFamily.dynamicUnipotentHaarDeterminant
    F G hG χ hZ hU cU hUc z hzN
  have hmod :
      rationalMinimalModulus i ν mP =
        HaarModulus.closedNormalizerCharacter _ hUc ⟨z ≫ iZ.hom.hom, hzN⟩ := by
    exact closedNormalizerCharacter_congr hUeq (isClosed_standardUnipotentPoints i ν ∅) hUc
      (standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅ mP.2) hzN hz.symm
  have hq : rationalPoints.map iP (rationalPoints.map (Dynamic.centralizerToParabolic hP hZ) z) = m := by
    change (z ≫ (Dynamic.centralizerToParabolic hP hZ).hom.hom) ≫ iP.hom.hom = m
    rw [Category.assoc, ← Grp.comp_hom_hom, Dynamic.centralizerToParabolic_comp]
    exact hz
  rw [hmod, hHaar, distribHaarChar_eq_residueNormalizedAbsoluteValue,
    ← Dynamic.adjointDeterminantCentralizerRestriction χ hP hZ hU cU,
    rationalCharacterEval_characterRestrict, ← Dynamic.adjointDeterminantPointValue_map hP, hq]

end Determinant

end Langlands.HarishChandraSchwartz
