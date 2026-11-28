import Langlands.Global.AdelicFiniteLeviFibreProjection
import Langlands.Global.AdelicParabolicConstantTermTransitivity
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Constant terms of smoothed families of cuspidal Levi classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSubgroupPoints PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "ι" => map F M G (fam.l J ≫ fam.p J)
local notation "hM" => IsRationalLeviSubgroup.isConnectedReductive
  (ParabolicRootPresentationData.IsCompatible.levi (fam.isCompatible J))

omit [NumberField F] in
private theorem exists_properLeviParabolic (Q : StandardIndex F G fam.i fam.ν) (hQ : Q < J) :
    ∃ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ M) (r : U ⟶ P),
      IsParabolicSubgroup p ∧ LeviSubgroup.IsGeometricUnipotentRadical r ∧
        SubgroupFunctor.range p ≠ ⊤ ∧ SubgroupFunctor.range (r ≫ p) =
          (SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)).comap (fam.l J ≫ fam.p J) := by
  let j := fam.l J ≫ fam.p J
  let : IsAffineHom (fam.M J).X.hom := (fam.isCompatible J).levi.isConnectedReductive.isAffineHom
  have hjc : IsClosedSubgroup j := (fam.isCompatible J).levi.isClosedSubgroup.comp
    (fam.isCompatible J).parabolic.isClosedSubgroup
  let : IsClosedImmersion j.hom.hom.left := hjc
  let hj : (standardLevi fam.i fam.ν J.val).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, (fam.isCompatible J).levi_eq⟩
  let iM := standardLeviTorusFactor fam.i fam.ν J.val hj
  have hiM : IsMaximalSplitTorus iM :=
    fam.maximalSplit.isMaximalSplitTorus_standardLeviTorusFactor fam.i fam.ν J.val hj hjc
  obtain ⟨hsimple, hνM, _⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter
    F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν fam.generic J.val J.2 M hM j hj hjc
  have hsub : Q.val ⊆ simpleRelativeRoots iM fam.ν := hsimple.symm ▸ hQ.le
  obtain ⟨⟨ζ, hζ⟩, hre⟩ := standardCocharacter F M hM fam.T iM hiM fam.ν hνM Q.val hsub
  let χ := CommGroupScheme.groupHom ζ ≫ iM
  let D := Dynamic.affineDecompositionModel χ
  obtain ⟨hPar, _, hUnip⟩ := hre ζ hζ
  have hd : IsClosedSubgroup D.parabolicHom := D.parabolic_closed
  let : IsAffineHom D.parabolic.X.hom := hd.isAffineHom
  refine ⟨D.parabolic, D.unipotent, D.parabolicHom, D.unipotentHom,
    isParabolicSubgroup_of_range_eq_dynamicParabolic hM D.parabolicHom hd χ D.parabolic_rep.2,
    (dynamicGeometricUnipotentRadical F M hM χ D.parabolic D.unipotent D.parabolicHom
      D.unipotentHom D.parabolic_rep D.unipotent_rep).leviSubgroup, ?_, ?_⟩
  · rw [D.parabolic_rep.2, ← hPar]
    intro htop
    apply (not_le_of_gt hQ)
    apply ((standardParabolicOrder F M hM fam.T iM hiM fam.ν hνM).1
      J.val Q.val hsimple.ge hsub).1.mpr
    rw [htop]
    intro X y _
    exact Subgroup.mem_top y
  · have hRes := (standardLeviStandardFamilies_inter fam.i fam.ν fam.connectedReductive
      fam.maximalSplit fam.generic J.val Q.val J.2 Q.2 hM j hj hjc).2.2
    rw [Set.inter_eq_right.mpr hQ.le, ← fam.range_radical_eq_standardUnipotent Q] at hRes
    exact D.unipotent_rep.2.trans (hUnip.symm.trans hRes)

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]

local notation "Pos" => intrinsicSubgroup F T
local notation "νP" => normalizedPositiveHaarMeasure F M T i hi I e hc
local notation "Q₊" => PositiveRationalQuotient F M T i
local notation "S" => fullAEL2CuspidalSubmodule F M parabolicDynamic hM T i hi I e hc

private theorem subgroupConstantTerm_leviFibreSmoothing_one
    {P U : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ M) (r : U ⟶ P)
    [IsAffine U.X.left] [IsClosedImmersion (r ≫ p).hom.hom.left]
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hproper : SubgroupFunctor.range p ≠ ⊤)
    (β : C_c(A, ℂ)) (w : Pos → S) (hw : Continuous w) (g : A) :
    subgroupConstantTerm F (r ≫ p) (fam.leviFibre J
      (fam.leviFibreSmoothing J T i hi I e hc β fun b => (w b).val) g) 1 = 0 := by
  let W := SubgroupFunctor.range (r ≫ p)
  let B := adelicPoints F M W
  let Y := AdelicSubgroupPoints.RationalQuotient F M W
  let Γ := AdelicSubgroupPoints.rationalSubgroup F M W
  let du := normalizedRationalQuotientHaarMeasure F M W
  let : IsClosed (B : Set AM) := isClosed_adelicPoints_range F M (r ≫ p)
  let : CompactSpace Y := compactSpace_rationalQuotient_range_unipotent F (r ≫ p)
    hr.1.smooth hr.1.connectedSpace hr.1.isUnipotent
  let : BorelSpace Y := rationalQuotientBorelSpace F M W
  let : IsProbabilityMeasure du := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F M W
  let := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e hc
  let : T2Space Pos := (positiveLogCoordinateEquiv F T I e).toHomeomorph.symm.t2Space
  let x (z : B) : A₁ := ⟨z.val, adelicPoints_le_normOneSubgroup F M W z.property⟩
  let E (z : B × Pos) :=
    fam.leviFibreSmoothingIntegrand J T i β g z.2 (x z.1) (w z.2).val
  have hx : Continuous x := continuous_subtype_val.subtype_mk _
  have hE : Continuous E :=
    Continuous.comp'
      (g := fun p : A × Pos × A₁ =>
        fam.leviFibreSmoothingIntegrand J T i β p.1 p.2.1 p.2.2 (w p.2.1).val)
      (f := fun p : B × Pos => ((g, p.2, x p.1) : A × Pos × A₁))
      (fam.continuous_leviFibreSmoothingIntegrand J T i hi I e hc β
        (fun b => (w b).val) (continuous_subtype_val.comp hw))
      (continuous_const.prodMk (continuous_snd.prodMk (hx.comp continuous_fst)))
  have hInv (r₀ : Γ) (z : B) (b : Pos) : E (r₀.val * z, b) = E (z, b) := by
    obtain ⟨a, ha⟩ := rationalImage_le_rationalSubgroup (r ≫ p)
      ((mem_rationalSubgroup_range_iff (r ≫ p) r₀.val).mp r₀.property)
    unfold E leviFibreSmoothingIntegrand
    change _ • normOnePartialConvolution T i _ ((w b).val : Q₊ → ℂ)
        ((r₀.val : AM) * (z : AM)) = _
    rw [← ha, normOnePartialConvolution_rational_mul]
  let f (q : Y) (b : Pos) := E (Quotient.out q, b)
  have hf : Continuous (Function.uncurry f) :=
    LeftCosetSpace.continuous_out_prod' Γ E hE hInv
  obtain ⟨D, hD, hSupp⟩ := fam.exists_compact_support_leviFibreSmoothingIntegrand
    J T i hi I e β (isCompact_singleton (x := g))
  have hfSupp : HasCompactSupport (Function.uncurry f) := by
    refine (isCompact_univ.prod hD).of_isClosed_subset (isClosed_tsupport _) ?_
    apply closure_minimal _ (isClosed_univ.prod hD.isClosed)
    intro z hz
    refine ⟨mem_univ _, by_contra fun h => hz (hSupp g rfl z.2 h (x (Quotient.out z.1)) (w z.2).val)⟩
  unfold subgroupConstantTerm
  change (∫ q : Y, fam.leviFibre J
      (fam.leviFibreSmoothing J T i hi I e hc β fun b => (w b).val) g
      ((Quotient.out q : B).val * 1) ∂du) = 0
  simp only [mul_one, leviFibre, leviFibreSmoothing]
  have hcov (q : Y) (b : Pos) :
      fam.leviFibreSmoothingIntegrand J T i β (ι (Quotient.out q : B).val * g) b 1 (w b).val =
        f q b := fam.leviFibreSmoothingIntegrand_mul_normOne J T i hc β g b (x (Quotient.out q)) (w b).val
  simp only [hcov]
  rw [integral_integral_swap_of_hasCompactSupport hf hfSupp]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun b => ?_)
  have hzero := congrFun
    (hasZeroProperParabolicConstantTerms_normOnePartialConvolution T i hi I e hc hM
      (fam.leviFibreSmoothingKernel J T i β g b) (w b).val (w b).property P U p r hp hr hproper)
    (1 : AM)
  unfold subgroupConstantTerm at hzero
  simp only [Pi.zero_apply, mul_one] at hzero
  simp only [f, E, leviFibreSmoothingIntegrand, integral_smul, Pi.zero_apply]
  dsimp only [x, du, Y, W]
  simpa only [smul_zero] using congrArg
    (fun z : ℂ => ((fam.leviModulus J (positivePointMap F M T i b) : ℝ)⁻¹) • z) hzero

/-- Smoothing a continuous family of cuspidal Levi classes has vanishing constant terms
along every strictly smaller standard parabolic. -/
theorem isCuspidalAlong_leviFibreSmoothing (β : C_c(A, ℂ)) (w : Pos → S) (hw : Continuous w) :
    fam.IsCuspidalAlong J (fam.leviFibreSmoothing J T i hi I e hc β fun b => (w b).val) := by
  intro Q hQ
  funext g
  obtain ⟨P, U, p, r, hp, hr, hproper, hR⟩ := fam.exists_properLeviParabolic J Q hQ
  let hru : IsClosedSubgroup (r ≫ p) := hr.1.isClosedSubgroup.comp hp.isClosedSubgroup
  let : IsClosedImmersion (r ≫ p).hom.hom.left := hru
  let : IsAffineHom U.X.hom := hru.isAffineHom_source
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F M (SubgroupFunctor.range (r ≫ p))) :=
    compactSpace_rationalQuotient_range_unipotent F (r ≫ p) hr.1.smooth hr.1.connectedSpace hr.1.isUnipotent
  let W := fun b => (w b).val
  have hcont := fam.continuous_leviFibreSmoothing J T i hi I e hc β W (continuous_subtype_val.comp hw)
  have hinv := fam.isLeftInvariantUnder_leviFibreSmoothing J T i hi I e hc β W
  have h := fam.subgroupConstantTerm_leviFibre (r ≫ p) hQ.le hR hcont hinv g 1
  rw [map_one, one_mul] at h
  exact h.symm.trans (fam.subgroupConstantTerm_leviFibreSmoothing_one
    J T i hi I e hc p r hp hr hproper β w hw g)

/-- The sum of the smoothed finite fibre vectors is cuspidal along the inducing parabolic. -/
theorem isCuspidalAlong_finiteLeviFibreProjection
    {n : ℕ} (β : Fin n → C_c(A, ℂ)) (k : Fin n → A) (φ : A → ℂ) (c : ℝ)
    (hw : ∀ j, Continuous (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j)) :
    fam.IsCuspidalAlong J (fam.finiteLeviFibreProjection J T i hi I e hc β k φ c) := by
  intro Q hQ
  let w (j : Fin n) := fam.finiteLeviFibreVector J T i hi I e hc β k φ c j
  let f (j : Fin n) := fam.leviFibreSmoothing J T i hi I e hc (β j) fun b => (w j b).val
  have hcusp (j : Fin n) : fam.constantTerm Q (f j) = 0 :=
    fam.isCuspidalAlong_leviFibreSmoothing J T i hi I e hc (β j) (w j) (hw j) Q hQ
  have hint (j : Fin n) : fam.HasIntegrableConstantTerm Q (f j) := by
    let r := fam.iU Q ≫ fam.p Q
    let hr := (fam.isUnipotentRadical Q).1
    let hc' : IsClosedSubgroup r := hr.isClosedSubgroup.comp (fam.isCompatible Q).parabolic.isClosedSubgroup
    let : IsClosedImmersion r.hom.hom.left := hc'
    have hcont := fam.continuous_leviFibreSmoothing J T i hi I e hc (β j) _
      (continuous_subtype_val.comp (hw j))
    have hinv := fam.isLeftInvariantUnder_leviFibreSmoothing J T i hi I e hc (β j)
      (fun b => (w j b).val)
    exact integrable_subgroupConstantTermIntegrand r hr.smooth hr.connectedSpace hr.isUnipotent hcont
      (fun x hx => hinv x (fam.rationalImage_radical_le_parabolicQuotientSubgroup hQ.le hx))
  have heq : fam.finiteLeviFibreProjection J T i hi I e hc β k φ c = (c : ℂ) • ∑ j, f j := by
    funext g
    simp only [finiteLeviFibreProjection, Pi.smul_apply, Finset.sum_apply, f, w]
  have hsum : fam.constantTerm Q (∑ j, f j) = ∑ j, fam.constantTerm Q (f j) := by
    funext g
    simp only [constantTerm, subgroupConstantTerm, Finset.sum_apply]
    exact integral_finsetSum _ fun j _ => hint j g
  rw [heq, constantTerm_const_smul, hsum]
  simp only [hcusp, Finset.sum_const_zero, smul_zero]

end Langlands.Global.StandardParabolicFamily
