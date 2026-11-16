import Langlands.Global.RankinSelberg.EqualAnalyticRegions

/-! # Mellin convergence from the adelic theta estimates -/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace AdelicSchwartzMellin

open EqualAnalytic

local instance mellinSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance mellinSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

/-- In rank one there are no chamber directions, so the constant function has
every chamber decay order with central exponent zero. -/
theorem pointDecay_one (Q : Set (AdelicGL F 1)) (K : ℝ) :
    PointDecay Q K (fun _ => (1 : ℂ)) 0 := by
  refine ⟨le_rfl, fun c _ => ⟨1, fun x _ q _ => ?_⟩⟩
  simp [spread]

/-- A rank-one theta series is Mellin integrable in a fixed right half-plane.
The nonoptimal constant `3` is independent of the dominated function. -/
theorem lintegral_thetaNorm_rpow_lt_top
    {Φ : RowVector F 1 → ℂ} (hΦc : Continuous Φ) (hΦ : IsRowDominated F 1 Φ)
    {σ : ℝ} (hσ : 3 < σ) :
    ∫⁻ q : AdelicGroupPoints.RationalQuotient F (Scheme F 1),
        ENNReal.ofReal (detNorm F 1 (Quotient.out q) ^ σ) *
          thetaNorm F 1 Φ (GeneralLinearGroupPoints.adelicEquiv F 1 (Quotient.out q))
      ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1) < ⊤ := by
  obtain ⟨Q, K, hQ, _, hdec⟩ := exists_siegelDecomposition F 1
  obtain ⟨L, hL⟩ := UnequalAnalytic.exists_abs_log_absDet_le (F := F) hQ
  have hL' : ∀ q ∈ Q, |Real.log (absDet F 1 q)| ≤ max L 0 :=
    fun q hq => (hL q hq).trans (le_max_left _ _)
  let V : Points F 1 → ℝ≥0∞ :=
    fun g => thetaNorm F 1 Φ (GeneralLinearGroupPoints.adelicEquiv F 1 g)
  have hVm : Measurable V := measurable_thetaNorm F 1 hΦc
  have hVr : ∀ (c : RationalGroupPoints F (Scheme F 1)) (g : Points F 1),
      V (AdelicGroupPoints.rational F (Scheme F 1) c * g) = V g := by
    intro c g
    change thetaNorm F 1 Φ (GeneralLinearGroupPoints.adelicHomeomorph F 1
      (AdelicGroupPoints.rational F (Scheme F 1) c * g)) = _
    rw [map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational,
      thetaNorm_rational_mul]
    rfl
  have hP := pointDecay_one F Q K
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (σ * Module.finrank ℚ F + 1)
  let N := max (Module.finrank ℚ F + 1) N₀
  have hN : 1 * Module.finrank ℚ F < N := by
    dsimp [N]
    omega
  have hNσ : σ * Module.finrank ℚ F + 1 ≤ (N : ℝ) :=
    hN₀.trans (by exact_mod_cast le_max_right (Module.finrank ℚ F + 1) N₀)
  obtain ⟨B, hB, hb⟩ := thetaNorm_chamber_le hΦ hQ N hN
  have hge := lintegral_region_ge_lt_top hQ hdec (le_max_right L 0) hL'
    (P := fun _ => (1 : ℂ)) continuous_const (fun _ _ => rfl) hP hVm hVr
    (Nat.cast_nonneg N) hB (fun x q hq => hb x q hq) (σ := σ) (by
      simpa only [Nat.cast_one, div_one, add_zero] using (by linarith : σ *
        (Module.finrank ℚ F : ℝ) + -(N : ℝ) ≤ -1))
  obtain ⟨B', hB', hb'⟩ := thetaNorm_chamber_le hΦ hQ (Module.finrank ℚ F + 1)
    (by omega)
  have hd : (1 : ℝ) ≤ Module.finrank ℚ F := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ F)
  have hσd : 1 ≤ σ * (Module.finrank ℚ F : ℝ) -
      ((Module.finrank ℚ F + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hlt := lintegral_region_lt_lt_top hQ hdec (le_max_right L 0) hL'
    (P := fun _ => (1 : ℂ)) continuous_const (fun _ _ => rfl) hP hVm hVr
    (Nat.cast_nonneg (Module.finrank ℚ F + 1)) hB'
    (fun x q hq => hb' x q hq) (σ := σ) (by
      simpa only [Nat.cast_one, div_one, sub_eq_add_neg, neg_zero, add_zero] using hσd)
  have hmge : Measurable fun q :
      AdelicGroupPoints.RationalQuotient F (Scheme F 1) =>
        regionGe (fun _ => (1 : ℂ)) σ V (Quotient.out q) := by
    let Γ := AdelicGroupPoints.rationalSubgroup F (Scheme F 1)
    have hi : ∀ (c : Γ) (g : Points F 1),
        regionGe (fun _ => (1 : ℂ)) σ V ((c : Points F 1) * g) =
          regionGe (fun _ => (1 : ℂ)) σ V g := by
      rintro ⟨_, c, rfl⟩ g
      exact regionGe_rational_mul (fun _ _ => rfl) σ hVr c g
    have he : (fun q : LeftCosetSpace Γ =>
        regionGe (fun _ => (1 : ℂ)) σ V (Quotient.out q)) =
        LeftCosetSpace.lift Γ (regionGe (fun _ => (1 : ℂ)) σ V) hi :=
      funext fun q => (UnequalAnalytic.lift_eq_out Γ _ hi q).symm
    rw [he]
    exact measurable_from_quotient.2 (measurable_regionGe continuous_const σ hVm)
  calc
    _ = ∫⁻ q : AdelicGroupPoints.RationalQuotient F (Scheme F 1),
        regionGe (fun _ => (1 : ℂ)) σ V (Quotient.out q) +
          regionLt (fun _ => (1 : ℂ)) σ V (Quotient.out q)
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1) := by
      apply lintegral_congr
      intro q
      have hp := UnequalAnalytic.detNorm_pos F (Quotient.out q)
      rw [Real.rpow_def_of_pos hp, mul_comm (Real.log _) σ]
      by_cases hq : 0 ≤ Real.log (detNorm F 1 (Quotient.out q))
      · simp only [regionGe, regionLt, Set.indicator, Set.mem_ofPred_eq, hq, not_lt.mpr hq,
          ↓reduceIte, enorm_one, one_mul, add_zero, V]
      · simp only [regionGe, regionLt, Set.indicator, Set.mem_ofPred_eq, hq, lt_of_not_ge hq,
          ↓reduceIte, enorm_one, one_mul, zero_add, V]
    _ = _ + _ := lintegral_add_left hmge _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hge, hlt⟩

/-- The normalization of the idele measure also applies to invariant kernels. -/
theorem lintegral_ideleDomain_eq
    (H : Points F 1 → ℝ≥0∞) (hHm : Measurable H)
    (hH : ∀ (c : ideleRational F) (g : Points F 1), H ((c : Points F 1) * g) = H g) :
    ∫⁻ z in ideleDomain F, H z ∂ideleMeasure F =
      (ideleSlabVolume F)⁻¹ *
        ∫⁻ q : AdelicGroupPoints.RationalQuotient F (Scheme F 1), H (Quotient.out q)
          ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1) := by
  let Hq := LeftCosetSpace.lift (ideleRational F) H hH
  have hHqm : Measurable Hq := measurable_from_quotient.2 hHm
  have he : (∫⁻ q, Hq q
      ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1)) =
      ∫⁻ z in ideleDomain F, H z ∂Measure.haar := by
    rw [AdelicGroupPoints.rationalQuotientHaarMeasure_eq F (Scheme F 1)
      (isFundamentalDomain_ideleDomain F Measure.haar), LeftCosetSpace.quotientMeasure,
      lintegral_map hHqm (LeftCosetSpace.measurable_mk _)]
    rfl
  rw [ideleMeasure, Measure.restrict_smul, lintegral_smul_measure, ← he]
  congr 1
  apply lintegral_congr
  intro q
  exact UnequalAnalytic.lift_eq_out _ H hH q

/-- A nonzero rational row of length one is a unit of the field. -/
def nonzeroRowEquiv : Fˣ ≃ {C : RatRow F 1 // C ≠ 0} where
  toFun f := ⟨fun _ _ => (f : F), by
    intro h
    exact f.ne_zero (congrFun (congrFun h 0) 0)⟩
  invFun C := Units.mk0 (C.1 0 0) (by
    intro h
    apply C.2
    ext i j
    change C.1 i j = 0
    simpa only [Subsingleton.elim i 0, Subsingleton.elim j 0] using h)
  left_inv f := by
    apply Units.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    ext i j
    exact congrArg₂ C.1 (Subsingleton.elim 0 i) (Subsingleton.elim 0 j)

/-- Reindex a rank-one theta series by the nonzero rational scalars. -/
theorem thetaNorm_one_eq_tsum (Φ : RowVector F 1 → ℂ) (z : Points F 1) :
    thetaNorm F 1 Φ (GeneralLinearGroupPoints.adelicEquiv F 1 z) =
      ∑' f : Fˣ, ‖Φ (lastRow F 0 (ratUnit F f * z))‖ₑ := by
  rw [thetaNorm_eq_tsum_subtype F 0, ← (nonzeroRowEquiv F).tsum_eq]
  apply tsum_congr
  intro f
  congr 2
  change _ = lastRow F 0
    (rationalPoint F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) f) * z)
  rw [lastRow_rationalPoint_mul]
  have hr : ((nonzeroRowEquiv F f).1 : RatRow F 1) =
      rowOf F 0 (Matrix.GeneralLinearGroup.scalar (Fin 1) f) := by
    ext i j
    change (f : F) = _
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simp [rowOf]
  rw [hr]

/-- Unfolding converts the Mellin integral over all ideles to a theta integral. -/
theorem lintegral_lastRow_rpow_eq
    {Φ : RowVector F 1 → ℂ} (hΦc : Continuous Φ) (σ : ℝ) :
    ∫⁻ z, ‖Φ (lastRow F 0 z)‖ₑ * ENNReal.ofReal (detNorm F 1 z ^ σ) ∂ideleMeasure F =
      (ideleSlabVolume F)⁻¹ *
        ∫⁻ q : AdelicGroupPoints.RationalQuotient F (Scheme F 1),
          ENNReal.ofReal (detNorm F 1 (Quotient.out q) ^ σ) *
            thetaNorm F 1 Φ (GeneralLinearGroupPoints.adelicEquiv F 1 (Quotient.out q))
          ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1) := by
  let W : Points F 1 → ℝ≥0∞ := fun z => ENNReal.ofReal (detNorm F 1 z ^ σ)
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp
    ((UnequalAnalytic.continuous_detNorm F 1).rpow_const
      (fun z => Or.inl (UnequalAnalytic.detNorm_pos F z).ne')).measurable
  have hWrat : ∀ (f : Fˣ) (z : Points F 1), W (ratUnit F f * z) = W z := by
    intro f z
    dsimp [W, ratUnit]
    rw [UnequalAnalytic.detNorm_rational_mul]
  let H : Points F 1 → ℝ≥0∞ := fun z =>
    W z * thetaNorm F 1 Φ (GeneralLinearGroupPoints.adelicEquiv F 1 z)
  have hHm : Measurable H := hWm.mul (measurable_thetaNorm F 1 hΦc)
  have hH : ∀ (c : ideleRational F) (z : Points F 1), H ((c : Points F 1) * z) = H z := by
    rintro ⟨_, c, rfl⟩ z
    dsimp [H, W]
    rw [UnequalAnalytic.detNorm_rational_mul, adelicEquiv_rational_mul F 0,
      thetaNorm_rational_mul]
  have hm : Measurable fun z : Points F 1 => ‖Φ (lastRow F 0 z)‖ₑ * W z :=
    (hΦc.comp (continuous_lastRow F 0)).measurable.enorm.mul hWm
  calc
    _ = ∑' f : Fˣ, ∫⁻ z in ideleDomain F,
        ‖Φ (lastRow F 0 (ratUnit F f * z))‖ₑ * W (ratUnit F f * z) ∂ideleMeasure F :=
      lintegral_idele_unfold F _
    _ = ∫⁻ z in ideleDomain F, ∑' f : Fˣ,
        ‖Φ (lastRow F 0 (ratUnit F f * z))‖ₑ * W (ratUnit F f * z) ∂ideleMeasure F :=
      (lintegral_tsum fun f =>
        (hm.comp (measurable_const_mul (ratUnit F f))).aemeasurable).symm
    _ = ∫⁻ z in ideleDomain F, H z ∂ideleMeasure F := by
      apply lintegral_congr
      intro z
      simp only [hWrat]
      rw [ENNReal.tsum_mul_right, mul_comm, ← thetaNorm_one_eq_tsum F Φ z]
    _ = _ := lintegral_ideleDomain_eq F H hHm hH

/-- A continuous dominated row function has a convergent full-idele Mellin
integral in the fixed half-plane `σ > 3`. -/
theorem lintegral_lastRow_rpow_lt_top
    {Φ : RowVector F 1 → ℂ} (hΦc : Continuous Φ) (hΦ : IsRowDominated F 1 Φ)
    {σ : ℝ} (hσ : 3 < σ) :
    ∫⁻ z, ‖Φ (lastRow F 0 z)‖ₑ * ENNReal.ofReal (detNorm F 1 z ^ σ) ∂ideleMeasure F < ⊤ := by
  rw [lintegral_lastRow_rpow_eq F hΦc]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 (ideleSlabVolume_ne_zero F)))
    (lintegral_thetaNorm_rpow_lt_top F hΦc hΦ hσ)

end AdelicSchwartzMellin

end Langlands.Global.RankinSelbergGlobal
