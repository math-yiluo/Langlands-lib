import Langlands.Global.AdelicIntertwiningReflectedRegionAnalytic
import Langlands.Global.AdelicIntertwiningReflectedHeight
import Langlands.Global.AdelicOppositeRadicalHeight
import Langlands.Global.AdelicIntertwiningModerateGrowthProof
import Langlands.Global.ProjectiveHeightSummability

/-! # Agreement of the intertwining integral on the reflected regular region -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints RepresentationGrowth

set_option maxHeartbeats 1500000 in
/-- The actual rational-quotient integral converges absolutely for sufficiently
regular reflected parameters. -/
theorem intertwiningReflectedRegionIntegrability :
    IntertwiningReflectedRegionIntegrabilityStatement.{u} := by
  intro F _ _ G P M U Q M' V A A' _ _ _ _ _ _ p _ iU l a r _ _ _ _ _ q _ iV l' _
    a' r' _ _ _ hA' hT' π' w c hG hU hV hπ' hw K hK hK' N dim rho hsmooth hcalc φ
    hKmax hrho hφ
  classical
  let : Smooth G.X.hom := hG.smooth
  let j := iV ≫ q
  let W := innerAdelicPoint F G w
  let Vₐ := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
  let Vᵣ := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)
  let Γ := intertwiningRationalSubgroup F p iU j W
  let measure := intertwiningMeasure F p iU j W
  let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hClosed
  let : LocallyCompactSpace Vₐ := hClosed.locallyCompactSpace
  let : PolishSpace Vₐ := hClosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_intertwiningRationalSubgroup F p iU j W)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hV.1.smooth
      hV.1.connectedSpace hV.1.isUnipotent
  have hInv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  have hmeas lam g : AEStronglyMeasurable (hK.intertwiningIntegrand iU j w φ lam g) measure :=
    (hK.continuous_intertwiningIntegrand iU j w hU.1.isUnipotent hInv hφ.2.1.1 lam g
      ).aestronglyMeasurable
  rcases Nat.eq_zero_or_pos N with hzero | hN
  · subst N
    let : Subsingleton (AdelicGroupPoints F G) :=
      subsingleton_adelicGroupPoints_of_closed_zeroMatrix rho hrho
    let : Subsingleton Vₐ := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
    have hΓ : Γ = Vᵣ := by
      ext x
      rw [Subsingleton.elim x 1]
      exact iff_of_true (Subgroup.one_mem Γ) (Subgroup.one_mem Vᵣ)
    have hFinite : IsFiniteMeasure measure := by
      have hProb := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure
        F G (SubgroupFunctor.range j)
      let : IsProbabilityMeasure
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (SubgroupFunctor.range j)) :=
        hProb
      have hfund (S T : Subgroup Vₐ) (hs : IsDiscrete (S : Set Vₐ))
          (ht : IsDiscrete (T : Set Vₐ)) (h : S = T) :
          LeftCosetSpace.fundamentalDomain S hs = LeftCosetSpace.fundamentalDomain T ht := by
        subst T
        rfl
      have hM : measure univ < ∞ := by
        change LeftCosetSpace.discreteQuotientMeasure Γ
          (isDiscrete_intertwiningRationalSubgroup F p iU j W)
          (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)) univ < ∞
        rw [LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure_univ,
          hfund _ _ _ (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _) hΓ]
        simpa only [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
          AdelicSubgroupPoints.rationalQuotientHaarMeasure, AdelicSubgroupPoints.normalizedHaarMeasure,
          LeftCosetSpace.haarQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
          LeftCosetSpace.quotientMeasure_univ, Measure.smul_apply] using
          (measure_lt_top (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
            (SubgroupFunctor.range j)) univ)
      exact ⟨hM⟩
    let : IsFiniteMeasure measure := hFinite
    refine ⟨0, fun lam _ g => ?_⟩
    have heq : hK.intertwiningIntegrand iU j w φ lam g =
        fun _ => hK.parameterTwist φ lam (1 : AdelicGroupPoints F G) := by
      funext x
      unfold IsIwasawaCompact.intertwiningIntegrand
      congr 1
      apply Subsingleton.elim
    change Integrable (hK.intertwiningIntegrand iU j w φ lam g) measure
    rw [heq]
    exact integrable_const _
  let H := adelicHeight F G rho
  have hH (z : AdelicGroupPoints F G) : 1 ≤ H z := one_le_adelicHeight F G rho hN z
  have hHpos (z : AdelicGroupPoints F G) : 0 < H z := zero_lt_one.trans_le (hH z)
  obtain ⟨C, d, b, hC, hb, hcompare⟩ :=
    exists_intertwiningReflectedHeightComparison r r' hK hK' hG hU hV hπ' hw rho hN hrho
  obtain ⟨s, hs, hφGrowth⟩ := HasModerateGrowthFunction.exists_compact_mul_le_height hφ.2.2.2.2
  obtain ⟨n, i, σ, hstab⟩ := Chevalley.exists_line_stabilizer F G P p
    r.isCompatible.parabolic.isClosedSubgroup
  let proj := parabolicRationalProjectiveEmbedding σ i hstab
  obtain ⟨χ, L, hχ⟩ := exists_height_le_sub_log_parabolicProjectiveEmbedding σ i hK hstab
  let τ : ComplexCharacterParameter F P := (-1 : ℂ) ⊗ₜ[ℤ] χ
  obtain ⟨Aχ, eχ, hAχ, heχ, hτ⟩ := hK.exists_norm_heightPower_le_adelicHeight rho hN hrho τ
  obtain ⟨t, ht, hsum⟩ := summable_projectivization_mulHeight_rpow F (Fin (n + 1))
  let S := s + eχ * t
  have hS : 0 ≤ S := add_nonneg hs (mul_nonneg heχ ht)
  obtain ⟨R, hdecay⟩ := hK'.exists_decay_on_oppositeRadical r' hA' hT' hG rho hN
    ((d : ℝ) * S) (mul_nonneg (Nat.cast_nonneg _) hS)
  refine ⟨R, fun lam hlam g => ?_⟩
  obtain ⟨B, hB, hDecay⟩ := hdecay (-weylParameter l c π' lam) hlam
  obtain ⟨F₀, hF₀, hGrowth⟩ := hφGrowth {g} isCompact_singleton
  obtain ⟨k, ⟨coords⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  obtain ⟨E, hE, hRight⟩ := hK.exists_norm_heightPower_mul_le (C := {g}) isCompact_singleton
    coords.toLinearMap (isCompact_singleton (x := coords.symm lam))
  obtain ⟨Ω, hΩ, hcover⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F j
    hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent
  obtain ⟨J₀, hJ₀⟩ := ((hΩ.image continuous_subtype_val).image
    (continuous_adelicHeight F G rho hN)).bddAbove
  let J := max J₀ 1
  have hJ : 0 < J := zero_lt_one.trans_le (le_max_right _ _)
  let weight (c : ParabolicRationalCosets F p) := (proj c).mulHeight ^ (-t)
  have hweight : Summable weight :=
    (hsum t le_rfl).comp_injective proj.injective
  have hcls : ∀ δ δ' : Vᵣ, intertwiningRationalCoset F p w δ =
      intertwiningRationalCoset F p w δ' → δ'.val * δ.val⁻¹ ∈ Γ := by
    intro δ δ' h
    have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf] at hrel
    obtain ⟨z, -, hz⟩ := hrel
    exact mul_inv_mem_intertwiningRationalSubgroup r w hG hU r'.isCompatible.parabolic hV
      (r'.isIso_subgroupMultiplication_of_radical hV) hw δ.2 δ'.2 ⟨z, hz⟩
  let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
  let : ν.IsHaarMeasure := Measure.IsHaarMeasure.smul _
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F G (SubgroupFunctor.range j))
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G (SubgroupFunctor.range j))
  let : Countable (AdelicGroupPoints.rationalSubgroup F G) :=
    LeftCosetSpace.countable_of_isDiscrete _ (AdelicGroupPoints.isDiscrete_rationalSubgroup F G)
  obtain ⟨maj, hmaj, hMaj⟩ := LeftCosetSpace.exists_integrable_majorant_of_cover
    Vᵣ Γ (isDiscrete_intertwiningRationalSubgroup F p iU j W) ν
    hΩ hΩ.measure_lt_top.ne (intertwiningRationalCoset F p w) hcls hweight
  let A₀ := F₀ * H W⁻¹ ^ s
  let A₁ := Real.exp L * Aχ * (H W⁻¹ * J) ^ eχ
  let A₂ := E * b lam * B
  let C₀ := A₀ * A₁ ^ t * A₂ * C ^ S
  have hA₀ : 0 ≤ A₀ := mul_nonneg hF₀.le (Real.rpow_nonneg (hHpos _).le _)
  have hA₁ : 0 ≤ A₁ := mul_nonneg (mul_nonneg (Real.exp_nonneg _) hAχ.le)
    (Real.rpow_nonneg (mul_nonneg (hHpos _).le hJ.le) _)
  have hA₂ : 0 ≤ A₂ := mul_nonneg (mul_nonneg hE.le (hb lam).le) hB.le
  have hConst : 0 ≤ A₀ * A₁ ^ t * A₂ :=
    mul_nonneg (mul_nonneg hA₀ (Real.rpow_nonneg hA₁ _)) hA₂
  have hC₀ : 0 ≤ C₀ := mul_nonneg hConst (Real.rpow_nonneg hC.le _)
  change Integrable (hK.intertwiningIntegrand iU j w φ lam g) measure
  refine (hmaj.const_mul C₀).mono' (hmeas lam g) (Eventually.of_forall fun x => ?_)
  let v : Vₐ := Quotient.out x
  obtain ⟨δ₀, hδ₀, hδΩ⟩ := hcover v
  let δ : Vᵣ := ⟨δ₀⁻¹, inv_mem hδ₀⟩
  let ω : Vₐ := δ₀ * v
  have hv : δ.val * ω = v := inv_mul_cancel_left δ₀ v
  have hx : LeftCosetSpace.mk Γ (δ.val * ω) = x := by
    rw [hv]
    exact LeftCosetSpace.mk_out _ x
  have hMajor := hMaj δ ω hδΩ
  rw [hx] at hMajor
  obtain ⟨v', y, hleft, hy, hSize, hPow⟩ := hcompare v.val v.property
  obtain ⟨u, hu⟩ := hleft
  change map F U G (iU ≫ p) u = W⁻¹ * v.val * (W⁻¹ * v')⁻¹ at hu
  have hvLeft : W⁻¹ * v.val = map F U G (iU ≫ p) u * (W⁻¹ * v') := by rw [hu]; group
  let qδ := intertwiningRationalCoset F p w δ
  let Z := (proj qδ).mulHeight
  have hZ : 0 < Z := Projectivization.mulHeight_pos _
  have hω : H (ω : AdelicGroupPoints F G) ≤ J :=
    (hJ₀ ⟨_, ⟨ω, hδΩ, rfl⟩, rfl⟩).trans (le_max_left _ _)
  have hZBound : Z ≤ A₁ * H v' ^ eχ := by
    obtain ⟨z, hz⟩ := inv_innerAdelicPoint_mul_mem_rationalSubgroup F w δ
    change rational F G z = W⁻¹ * δ.val.val at hz
    have hq : qδ = Quotient.mk _ (⟨rational F G z, ⟨z, rfl⟩⟩ :
        AdelicGroupPoints.rationalSubgroup F G) := by
      unfold qδ intertwiningRationalCoset
      congr 1
      exact Subtype.ext hz.symm
    have hχz := hχ z
    rw [← hq, Projectivization.logHeight_eq_log_mulHeight] at hχz
    have harg : rational F G z =
        map F U G (iU ≫ p) u * (W⁻¹ * v' * (ω : AdelicGroupPoints F G)⁻¹) := by
      have hval : δ.val.val * ω.val = v.val := congrArg Subtype.val hv
      rw [hz]
      calc
        W⁻¹ * δ.val.val = (W⁻¹ * v.val) * ω.val⁻¹ := by rw [← hval]; group
        _ = _ := by rw [hvLeft]; group
    let z' := W⁻¹ * v' * ω.val⁻¹
    have hRemove : hK.height (rational F G z) = hK.height z' := by
      rw [harg, map_comp_apply_of_hom iU, hK.height_unipotent_mul hU.1.isUnipotent]
    have hτz : ‖hK.heightPower τ z'‖ = Real.exp (-hK.height z' χ) := by
      simp [IsIwasawaCompact.heightPower, τ, complexParameterPairing_tmul, Complex.norm_exp]
    have hExp : Z ≤ Real.exp L * ‖hK.heightPower τ z'‖ := by
      rw [hτz, ← Real.exp_add, ← Real.exp_log hZ]
      apply Real.exp_le_exp.mpr
      rw [hRemove] at hχz
      exact le_sub_comm.mp hχz
    have hHarg : H z' ≤ (H W⁻¹ * J) * H v' := by
      calc
        _ ≤ H (W⁻¹ * v') * H ω.val⁻¹ := adelicHeight_mul_le F G rho hN _ _
        _ ≤ (H W⁻¹ * H v') * J := by
          rw [show H ω.val⁻¹ = H ω.val from adelicHeight_inv F G rho _]
          exact mul_le_mul (adelicHeight_mul_le F G rho hN _ _) hω (hHpos _).le
            (mul_nonneg (hHpos _).le (hHpos _).le)
        _ = _ := by ring
    calc
      _ ≤ Real.exp L * ‖hK.heightPower τ z'‖ := hExp
      _ ≤ Real.exp L * (Aχ * (((H W⁻¹ * J) * H v') ^ eχ)) := by
        refine mul_le_mul_of_nonneg_left ((hτ z').trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hHpos _).le hHarg heχ) hAχ.le)) (Real.exp_nonneg _)
      _ = _ := by rw [Real.mul_rpow (mul_nonneg (hHpos _).le hJ.le) (hHpos _).le]; dsimp [A₁]; ring
  have hPhi : ‖φ (W⁻¹ * v.val * g)‖ ≤ A₀ * H v' ^ s := by
    have hφEq := hInv _ ⟨u, rfl⟩ (W⁻¹ * v' * g)
    change φ (map F U G (iU ≫ p) u * (W⁻¹ * v' * g)) = _ at hφEq
    rw [hvLeft, mul_assoc, hφEq]
    calc
      _ ≤ F₀ * H (W⁻¹ * v') ^ s := by
        simpa only [adelicHeightAtLeastOne_eq hN] using hGrowth (W⁻¹ * v') g (mem_singleton g)
      _ ≤ F₀ * (H W⁻¹ * H v') ^ s := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hHpos _).le (adelicHeight_mul_le F G rho hN _ _) hs) hF₀.le
      _ = _ := by rw [Real.mul_rpow (hHpos _).le (hHpos _).le]; dsimp [A₀]; ring
  have hRight' := hRight (W⁻¹ * v.val) g (mem_singleton g) (coords.symm lam) (mem_singleton _)
  simp only [LinearEquiv.coe_coe, coords.apply_symm_apply] at hRight'
  have hPower : ‖hK.heightPower lam (W⁻¹ * v.val * g)‖ ≤ A₂ * H y ^ (-((d : ℝ) * S)) := by
    refine hRight'.trans ?_
    rw [hPow lam]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hDecay y hy) (hb lam).le)
      hE.le).trans_eq (by dsimp [A₂]; ring)
  have hBoth : ‖hK.intertwiningIntegrand iU j w φ lam g x‖ * Z ^ t ≤ C₀ := by
    change ‖φ (W⁻¹ * v.val * g) * hK.heightPower lam (W⁻¹ * v.val * g)‖ * Z ^ t ≤ C₀
    rw [norm_mul]
    have hZt := Real.rpow_le_rpow hZ.le hZBound ht
    have hSizeS := Real.rpow_le_rpow (hHpos _).le hSize hS
    have hYs : 0 ≤ H y ^ (-((d : ℝ) * S)) := Real.rpow_nonneg (hHpos _).le _
    have hvS : 0 ≤ A₀ * H v' ^ s := mul_nonneg hA₀ (Real.rpow_nonneg (hHpos _).le _)
    calc
      _ ≤ (A₀ * H v' ^ s) * (A₂ * H y ^ (-((d : ℝ) * S))) * (A₁ * H v' ^ eχ) ^ t := by
        exact mul_le_mul (mul_le_mul hPhi hPower (norm_nonneg _) hvS) hZt
          (Real.rpow_nonneg hZ.le _) (mul_nonneg hvS (mul_nonneg hA₂ hYs))
      _ = (A₀ * A₁ ^ t * A₂) * (H v' ^ S * H y ^ (-((d : ℝ) * S))) := by
        have hSumPow : H v' ^ S = H v' ^ s * (H v' ^ eχ) ^ t := by
          dsimp only [S]
          rw [Real.rpow_add (hHpos _), Real.rpow_mul (hHpos _).le]
        rw [Real.mul_rpow hA₁ (Real.rpow_nonneg (hHpos _).le _), hSumPow]
        ring
      _ ≤ (A₀ * A₁ ^ t * A₂) * ((C * H y ^ d) ^ S * H y ^ (-((d : ℝ) * S))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSizeS hYs) hConst
      _ = _ := by
        rw [Real.mul_rpow hC.le (pow_nonneg (hHpos _).le _), ← Real.rpow_natCast (H y) d,
          ← Real.rpow_mul (hHpos _).le]
        have hcancel : H y ^ ((d : ℝ) * S) * H y ^ (-((d : ℝ) * S)) = 1 := by
          rw [← Real.rpow_add (hHpos _), add_neg_cancel, Real.rpow_zero]
        rw [mul_assoc (C ^ S), hcancel, mul_one]
  have hWeight : ‖hK.intertwiningIntegrand iU j w φ lam g x‖ ≤ C₀ * weight qδ := by
    change _ ≤ C₀ * Z ^ (-t)
    rw [Real.rpow_neg hZ.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr hBoth
  exact hWeight.trans (mul_le_mul_of_nonneg_left hMajor hC₀)

/-- The normalized intertwining integral agrees with any finite meromorphic
expansion on the sufficiently regular reflected region. -/
theorem intertwiningReflectedRegionAgreement : IntertwiningReflectedRegionAgreementStatement.{u} :=
  intertwiningReflectedRegionAgreement_of_integrability intertwiningReflectedRegionIntegrability

end Langlands.Global
