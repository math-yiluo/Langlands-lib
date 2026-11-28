import Langlands.Global.AdelicLeviFibreSmoothing
import Langlands.Global.AdelicNormOnePartialConvolutionGrowth
import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.AdelicLeviCuspFormMajorantProof
import Langlands.Global.AdelicLeviFibreConstantTerm

/-! # Moderate growth of smoothed Levi classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise Topology NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "ι" => map F M G (fam.l J ≫ fam.p J)
local notation "ιU" => map F (fam.U J) G (fam.iU J ≫ fam.p J)
local notation "Q" => PositiveRationalQuotient F M T i
local notation "V" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F M T i)
local notation "Pos" => intrinsicSubgroup F T
local notation "pp" => positivePointMap F M T i
local notation "πP" => positiveFactor F M T i hi I e
local notation "νP" => normalizedPositiveHaarMeasure F M T i hi I e hc
local notation "δ" => fam.leviModulus J

variable [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]

include hi e hc in
/-- On a compact set of ambient parameters, recentered smoothing is bounded by a product of
powers of the positive and norm-one Levi heights. -/
theorem exists_leviFibreSmoothing_mul_levi_bound {N : ℕ} (rho : MatrixRepresentation M (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) (β : C_c(A, ℂ)) (w : Pos → V)
    (B : ℝ) (hB : 0 ≤ B) (r : ℕ) (hw : ∀ b, ‖w b‖ ≤ B * adelicHeight F M rho (pp b) ^ r)
    {C : Set A} (hC : IsCompact C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ d : ℕ, ∀ g ∈ C, ∀ (a : Pos) (x : A₁),
      ‖fam.leviFibreSmoothing J T i hi I e hc β w (ι (pp a * (x : AM)) * g)‖ ≤
        L * adelicHeight F M rho (pp a) ^ r * adelicHeight F M rho (x : AM) ^ d := by
  let := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e hc
  let : T2Space Pos := (positiveLogCoordinateEquiv F T I e).toHomeomorph.symm.t2Space
  let H := adelicHeight F M rho
  have hH (m : AM) : 0 ≤ H m := zero_le_one.trans (one_le_adelicHeight F M rho hN m)
  obtain ⟨D, hD, hSupp⟩ := fam.exists_compact_support_leviFibreSmoothingIntegrand J T i hi I e β hC
  obtain ⟨E, hE, hSuppL⟩ := fam.exists_compact_tsupport_radicalKernelCc J β hC
    (isCompact_singleton (x := (1 : A)))
  let S : Set AM := E⁻¹ * (pp '' D)
  have hS : IsCompact S := hE.inv.mul (hD.image (pp).continuous)
  have hLcont : Continuous fun p : A × AM => ‖fam.radicalKernel J β p.1 1 p.2‖ :=
    ((fam.continuous_radicalKernel J β).comp (continuous_fst.prodMk
      (continuous_const.prodMk continuous_snd))).norm
  obtain ⟨M₀, hM₀⟩ := ((hC.prod hE).image hLcont).bddAbove
  let U := max M₀ 0
  have hU : 0 ≤ U := le_max_right _ _
  obtain ⟨R, hR, d, hBound⟩ := exists_normOnePartialConvolution_bound T i hi I e hc rho hN hrho S hS U hU
  let W (b : Pos) : ℝ := (δ (pp b) : ℝ)⁻¹ * H (pp b) ^ r
  have hδ (b : Pos) : 0 < (δ (pp b) : ℝ) := NNReal.coe_pos.mpr (fam.leviModulus_pos J (pp b))
  have hW : Continuous W :=
    ((NNReal.continuous_coe.comp ((fam.continuous_leviModulus J).comp (pp).continuous)).inv₀
      fun b => (hδ b).ne').mul (((continuous_adelicHeight F M rho hN).comp (pp).continuous).pow r)
  obtain ⟨V₀, hV₀⟩ := (hD.image hW).bddAbove
  let V₁ := max V₀ 0
  have hV₁ : 0 ≤ V₁ := le_max_right _ _
  refine ⟨R * B * V₁ * (νP).real D,
    mul_nonneg (mul_nonneg (mul_nonneg hR hB) hV₁) measureReal_nonneg, d, fun g hg a x => ?_⟩
  rw [fam.leviFibreSmoothing_mul_levi J T i hi I e hc β w g a x]
  let L := fam.radicalKernelCc J β g 1
  let K (b : Pos) := fam.leviFibreSmoothingKernel J T i β g b
  have hLsupp : tsupport L ⊆ E := hSuppL g hg 1 rfl
  have hKsupp (b : Pos) (hb : b ∈ D) : tsupport (K b) ⊆ S := by
    refine closure_minimal (fun z hz => ?_) hS.isClosed
    let m := pp b * z⁻¹
    have hm : L m ≠ 0 := by
      intro hm
      apply hz
      change starRingEnd ℂ (L m) = 0
      rw [hm, map_zero]
    refine ⟨m⁻¹, Set.inv_mem_inv.mpr (hLsupp (subset_tsupport _ hm)), pp b, ⟨b, hb, rfl⟩, ?_⟩
    dsimp only [m]
    group
  have hKU (b : Pos) (z : AM) : ‖K b z‖ ≤ U := by
    let m := pp b * z⁻¹
    change ‖starRingEnd ℂ (L m)‖ ≤ U
    rw [Complex.norm_conj]
    by_cases hm : m ∈ E
    · exact (hM₀ ⟨(g, m), ⟨hg, hm⟩, rfl⟩).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport (fun hm' => hm (hLsupp hm')), norm_zero]
      exact hU
  let Dbound := R * B * V₁ * H (pp a) ^ r * H (x : AM) ^ d
  have hdom : Integrable (D.indicator fun _ => Dbound) νP :=
    (integrableOn_const hD.measure_lt_top.ne).integrable_indicator hD.measurableSet
  calc
    _ ≤ ∫ b, D.indicator (fun _ => Dbound) b ∂νP := by
      refine norm_integral_le_of_norm_le hdom (Eventually.of_forall fun b => ?_)
      change ‖fam.leviFibreSmoothingIntegrand J T i β g b x (w (a * b))‖ ≤
        D.indicator (fun _ => Dbound) b
      by_cases hb : b ∈ D
      · rw [indicator_of_mem hb]
        unfold leviFibreSmoothingIntegrand
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hδ b).le)]
        have hab : ‖w (a * b)‖ ≤ B * (H (pp a) * H (pp b)) ^ r := by
          refine (hw _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH _) ?_ _) hB)
          rw [map_mul]
          exact adelicHeight_mul_le F M rho hN _ _
        calc
          _ ≤ (δ (pp b) : ℝ)⁻¹ * (R * H (x : AM) ^ d * (B * (H (pp a) * H (pp b)) ^ r)) :=
            mul_le_mul_of_nonneg_left
              ((hBound (K b) (hKsupp b hb) (hKU b) x (w (a * b))).trans
                (mul_le_mul_of_nonneg_left hab (mul_nonneg hR (pow_nonneg (hH _) _))))
              (inv_nonneg.mpr (hδ b).le)
          _ = R * B * W b * H (pp a) ^ r * H (x : AM) ^ d := by
            rw [mul_pow]; dsimp only [W]; ring
          _ ≤ Dbound := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ((hV₀ ⟨b, hb, rfl⟩).trans (le_max_left _ _))
                (mul_nonneg hR hB)) (pow_nonneg (hH _) _)) (pow_nonneg (hH _) _)
      · rw [indicator_of_notMem hb, hSupp g hg b hb x, norm_zero]
    _ = _ := by
      rw [integral_indicator_const _ hD.measurableSet, smul_eq_mul]
      dsimp only [Dbound]; ring

include hi e hc in
/-- A polynomial norm bound for the family on the positive torus gives moderate growth of
its smoothing on the ambient group. -/
theorem hasHeightGrowth_leviFibreSmoothing {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) (K : Subgroup A) (hK : IsIwasawaCompact (fam.p J) K)
    (β : C_c(A, ℂ)) (w : Pos → V) (B : ℝ) (hB : 0 ≤ B) (r : ℕ)
    (hw : ∀ b, ‖w b‖ ≤ B * adelicHeight F M ((fam.l J ≫ fam.p J) ≫ rho) (pp b) ^ r) :
    HasHeightGrowth rho (fam.leviFibreSmoothing J T i hi I e hc β w) := by
  let rhoM := (fam.l J ≫ fam.p J) ≫ rho
  let rhoP := fam.p J ≫ rho
  let H := adelicHeight F G rho
  let HM := adelicHeight F M rhoM
  let HP := adelicHeight F (fam.P J) rhoP
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : IsClosedImmersion (fam.l J).hom.hom.left := (fam.isCompatible J).levi.isClosedSubgroup
  let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  have hM : IsClosedSubgroup rhoM := by
    change IsClosedImmersion ((fam.l J ≫ fam.p J) ≫ rho).hom.hom.left
    simp only [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  have hP : IsClosedSubgroup rhoP := by
    change IsClosedImmersion (fam.p J ≫ rho).hom.hom.left
    simp only [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  have := fam.isIso_subgroupMultiplication_levi_radical J
  let π := leviRetraction (fam.l J) (fam.iU J) (fam.isUnipotentRadical J).1.isNormal
  obtain ⟨L, hL, d, hSmooth⟩ := fam.exists_leviFibreSmoothing_mul_levi_bound J T i hi I e hc
    rhoM hN hM β w B hB r hw hK.isCompact
  obtain ⟨D, hD, n, hPos⟩ := exists_adelicHeight_positivePointMap_le F rhoM hN hM T i e
  obtain ⟨E, hE, j, hLevi⟩ := closedImmersionAdelicHeightDomination F (fam.P J) N N
    rhoP (π ≫ rhoM) hN hN hP
  obtain ⟨L₀, hL₀⟩ := (hK.isCompact.image (continuous_adelicHeight F G rho hN)).bddAbove
  let C := E * max L₀ 1 ^ j
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans hE) (pow_nonneg (zero_le_one.trans (le_max_right _ _)) _)
  let s := n * r + (n + 1) * d
  refine ⟨L * D ^ (r + d) * C ^ s, (j * s : ℕ), by positivity,
    Nat.cast_nonneg _, fun g => ?_⟩
  rw [Real.rpow_natCast]
  obtain ⟨q, k, hk, hg⟩ := hK.exists_eq g
  let m := fam.leviProjection J q
  let ml := map F M (fam.P J) (fam.l J) m
  have hker : fam.leviProjection J (q * ml⁻¹) = 1 := by
    rw [map_mul, map_inv, show fam.leviProjection J ml = m from fam.leviProjection_levi J m,
      ← show m = fam.leviProjection J q from rfl, mul_inv_cancel]
  obtain ⟨u₀, hu₀⟩ := (comp_leviRetraction_eq_one_iff (fam.l J) (fam.iU J)
    (fam.isUnipotentRadical J).1.isNormal (q * ml⁻¹)).mp hker
  have hq : q = map F (fam.U J) (fam.P J) (fam.iU J) u₀ * ml := by
    change map F (fam.U J) (fam.P J) (fam.iU J) u₀ = q * ml⁻¹ at hu₀
    rw [hu₀, inv_mul_cancel_right]
  have hg' : g = ιU u₀ * (ι m * k) := by
    rw [← hg, hq, map_mul, ← map_comp_apply_of_hom (fam.iU J), mul_assoc]
    rw [show map F (fam.P J) G (fam.p J) ml = ι m from
      (map_comp_apply_of_hom (fam.l J) m).symm]
  let a := πP m
  let x := normOneFactor F M T i hi I e m
  have hax : pp a * (x : AM) = m := positivePointMap_mul_normOneFactor F M T i hi I e m
  have hf : fam.leviFibreSmoothing J T i hi I e hc β w g =
      fam.leviFibreSmoothing J T i hi I e hc β w (ι m * k) := by
    rw [hg']
    exact fam.isLeftInvariantUnder_leviFibreSmoothing J T i hi I e hc β w (ιU u₀)
      (Subgroup.mem_sup_left ⟨u₀, rfl⟩) (ι m * k)
  rw [hf]
  have hhm : 0 ≤ HM m := zero_le_one.trans (one_le_adelicHeight F M rhoM hN m)
  have hha : 0 ≤ HM (pp a) := zero_le_one.trans (one_le_adelicHeight F M rhoM hN _)
  have hhx : 0 ≤ HM (x : AM) := zero_le_one.trans (one_le_adelicHeight F M rhoM hN _)
  have hhg : 0 ≤ H g := zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  have hPa : HM (pp a) ≤ D * HM m ^ n := by simpa only [hax] using hPos a x
  have hNx : HM (x : AM) ≤ D * HM m ^ (n + 1) := by
    change HM ((pp a)⁻¹ * m) ≤ _
    calc
      _ ≤ HM ((pp a)⁻¹) * HM m := adelicHeight_mul_le F M rhoM hN _ _
      _ ≤ D * HM m ^ n * HM m := by
        rw [show HM ((pp a)⁻¹) = HM (pp a) from adelicHeight_inv F M rhoM _]
        exact mul_le_mul_of_nonneg_right hPa hhm
      _ = _ := by rw [pow_succ, mul_assoc]
  have hpk : map F (fam.P J) G (fam.p J) q = g * k⁻¹ := by rw [← hg, mul_inv_cancel_right]
  have hHP : HP q = H (g * k⁻¹) := by
    rw [← hpk]
    exact (adelicHeight_map_eq_adelicHeight_comp (fam.p J) rho q).symm
  have hHQ : HP q ≤ H g * max L₀ 1 := by
    rw [hHP]
    exact (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_left
      ((hL₀ ⟨k⁻¹, K.inv_mem hk, rfl⟩).trans (le_max_left _ _)) hhg)
  have hHM : HM m ≤ C * H g ^ j := by
    calc
      HM m = adelicHeight F (fam.P J) (π ≫ rhoM) q := adelicHeight_map_eq_adelicHeight_comp π rhoM q
      _ ≤ E * HP q ^ j := hLevi q
      _ ≤ E * (H g * max L₀ 1) ^ j := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (one_le_adelicHeight F (fam.P J) rhoP hN q)) hHQ j)
        (zero_le_one.trans hE)
      _ = _ := by dsimp only [C]; rw [mul_pow]; ring
  calc
    _ ≤ L * HM (pp a) ^ r * HM (x : AM) ^ d := by simpa only [hax] using hSmooth k hk a x
    _ ≤ L * (D * HM m ^ n) ^ r * (D * HM m ^ (n + 1)) ^ d :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hha hPa _) hL)
        (pow_le_pow_left₀ hhx hNx _) (pow_nonneg hhx _) (mul_nonneg hL (pow_nonneg (mul_nonneg hD (pow_nonneg hhm _)) _))
    _ = L * D ^ (r + d) * HM m ^ s := by
      dsimp only [s]
      simp only [mul_pow, ← pow_mul, pow_add]
      ring
    _ ≤ L * D ^ (r + d) * (C * H g ^ j) ^ s :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hhm hHM _) (mul_nonneg hL (pow_nonneg hD _))
    _ = (L * D ^ (r + d) * C ^ s) * H g ^ (j * s) := by
      simp only [mul_pow, pow_mul, mul_assoc]

end Langlands.Global.StandardParabolicFamily
