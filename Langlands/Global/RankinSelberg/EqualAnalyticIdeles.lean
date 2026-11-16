import Langlands.Global.RankinSelberg.EqualUnfoldingIdele
import Langlands.Global.RankinSelberg.EqualIntegrals
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints
import Langlands.Global.RankinSelberg.UnequalAnalyticDecay
import Langlands.Global.RankinSelberg.EqualAnalyticFundamentalDomain
import Langlands.Global.LeftCosetHaarMeasure

/-! # The idele measure `d^×a` and the norm

On `𝔸^× = GL_1(𝔸)` (the points `Points F 1`), with the rational subgroup `F^×`, its Library
fundamental domain `D₁` and the measure `ideleMeasure F` of `EqualIntegrals`:

* `GL_1(𝔸)` is commutative (`points_one_mul_comm`), and `normScale y` (archimedean components
  `exp (y / [F:ℚ])`, finite part `1`) is a continuous homomorphism `ℝ → 𝔸^×` with
  `|normScale y| = exp y`.
* The idele slab `F^× \ {1 ≤ |a| < e}` has positive finite Haar volume (`ideleSlabVolume_ne_zero`,
  `ideleSlabVolume_ne_top`); so `D₁ ∩ {1 ≤ |a| < e}` has `ideleMeasure` one.
* **`log |·|` carries `ideleMeasure` on `D₁` to Lebesgue measure** (`map_logNorm_eq_volume`).
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj ENNReal Pointwise

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance idelesSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance idelesSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F
local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-! ### The archimedean scaling `ℝ → 𝔸^×` -/

/-- The idele with every archimedean component `exp (y / [F:ℚ])` and finite part `1`. -/
def normScale (y : ℝ) : Points F 1 :=
  (e 1).symm (AdelicGL.ofInfinite F 1 (torInf F 1 fun _ => y / Module.finrank ℚ F))

theorem normScale_add (y y' : ℝ) : normScale F (y + y') = normScale F y * normScale F y' := by
  simp only [normScale, ← map_mul, ← torInf_add]
  congr 3
  funext i
  simp only [Pi.add_apply, add_div]

theorem normScale_zero : normScale F 0 = 1 := by
  have h := normScale_add F 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem continuous_normScale : Continuous (normScale F) :=
  (e 1).symm.continuous.comp ((AdelicGL.ofInfinite F 1).continuous.comp
    ((continuous_torInf F 1).comp (continuous_pi fun _ => continuous_id.div_const _)))

theorem detNorm_normScale (y : ℝ) : detNorm F 1 (normScale F y) = Real.exp y := by
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  show absDet F 1 (e 1 (normScale F y)) = Real.exp y
  rw [normScale, ContinuousMulEquiv.apply_symm_apply, absDet_ofInfinite_torInf,
    Fin.sum_univ_one, ← Real.exp_nat_mul, mul_div_cancel₀ _ hd]

theorem detNorm_one_mul (a b : Points F 1) :
    detNorm F 1 (a * b) = detNorm F 1 a * detNorm F 1 b :=
  UnequalAnalytic.detNorm_mul F a b

/-! ### The rational subgroup and its fundamental domain -/

/-- The principal ideles `F^× ⊆ 𝔸^×`. -/
abbrev ideleRational : Subgroup (Points F 1) :=
  AdelicGroupPoints.rationalSubgroup F (Scheme F 1)

theorem isDiscrete_ideleRational : IsDiscrete (ideleRational F : Set (Points F 1)) :=
  AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F 1)

instance countable_ideleRational : Countable (ideleRational F) :=
  LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_ideleRational F)

/-- The Library fundamental domain `D₁` of `F^×` in `𝔸^×`. -/
def ideleDomain : Set (Points F 1) :=
  LeftCosetSpace.fundamentalDomain (ideleRational F) (isDiscrete_ideleRational F)

theorem measurableSet_ideleDomain : MeasurableSet (ideleDomain F) :=
  LeftCosetSpace.measurableSet_fundamentalDomain _ _

theorem isFundamentalDomain_ideleDomain (ν : Measure (Points F 1)) :
    IsFundamentalDomain (ideleRational F) (ideleDomain F) ν :=
  LeftCosetSpace.isFundamentalDomain _ _ ν

theorem detNorm_ideleRational_mul (c : ideleRational F) (a : Points F 1) :
    detNorm F 1 ((c : Points F 1) * a) = detNorm F 1 a := by
  obtain ⟨_, c, rfl⟩ := c
  exact UnequalAnalytic.detNorm_rational_mul F c a

/-- A set of ideles defined through the norm is `F^×`-invariant. -/
theorem detNorm_preimage_invariant (B : Set ℝ) (c : ideleRational F) (a : Points F 1) :
    (c : Points F 1) * a ∈ (fun z => detNorm F 1 z) ⁻¹' B ↔
      a ∈ (fun z => detNorm F 1 z) ⁻¹' B := by
  simp only [mem_preimage, detNorm_ideleRational_mul]

theorem measurable_detNorm_one : Measurable fun z : Points F 1 => detNorm F 1 z :=
  (UnequalAnalytic.continuous_detNorm F 1).measurable

/-- The preimage of the image of a `Γ`-invariant set under the quotient map is the set. -/
theorem preimage_image_mk_of_invariant {H : Type*} [Group H] (Γ : Subgroup H) {A : Set H}
    (hA : ∀ (c : Γ) (x : H), (c : H) * x ∈ A ↔ x ∈ A) :
    LeftCosetSpace.mk Γ ⁻¹' (LeftCosetSpace.mk Γ '' A) = A := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy := (LeftCosetSpace.mk_eq_mk_iff Γ y x).1 hyx
    have h := (hA ⟨x * y⁻¹, hxy⟩ y).2 hy
    simpa only [inv_mul_cancel_right] using h
  · intro hx
    exact ⟨x, hx, rfl⟩

/-! ### The slab volume -/

/-- The idele slab `{1 ≤ |a| < e}`. -/
def ideleSlab : Set (Points F 1) :=
  (fun z => detNorm F 1 z) ⁻¹' Ico 1 (Real.exp 1)

theorem measurableSet_ideleSlab : MeasurableSet (ideleSlab F) :=
  measurableSet_Ico.preimage (measurable_detNorm_one F)

theorem ideleSlabVolume_eq :
    ideleSlabVolume F = Measure.haar (ideleDomain F ∩ ideleSlab F) := by
  rw [ideleSlabVolume, AdelicGroupPoints.rationalQuotientHaarMeasure_eq F (Scheme F 1)
    (isFundamentalDomain_ideleDomain F Measure.haar)]
  have hslab : determinantSlab F 1 1 (Real.exp 1) =
      LeftCosetSpace.mk (ideleRational F) '' ideleSlab F := rfl
  rw [hslab, LeftCosetSpace.quotientMeasure_apply _ _ _
    (LeftCosetSpace.measurableSet_image_mk _ (measurableSet_ideleSlab F)),
    preimage_image_mk_of_invariant (A := ideleSlab F) _
      (fun c x => detNorm_preimage_invariant F _ c x), inter_comm]

/-! ### The normalized idele measure -/

instance ideleMeasure_isMulLeftInvariant : (ideleMeasure F).IsMulLeftInvariant := by
  unfold ideleMeasure; infer_instance

instance ideleMeasure_sFinite : SFinite (ideleMeasure F) := by
  unfold ideleMeasure; infer_instance

theorem ideleMeasure_slab : ideleMeasure F (ideleDomain F ∩ ideleSlab F) = 1 := by
  rw [ideleMeasure, Measure.smul_apply, smul_eq_mul, ← ideleSlabVolume_eq]
  exact ENNReal.inv_mul_cancel (ideleSlabVolume_ne_zero F) (ideleSlabVolume_ne_top F)

/-- Translation by `normScale y` inside the fundamental domain. -/
theorem ideleMeasure_inter_preimage_normScale (y : ℝ) {T : Set (Points F 1)}
    (hT : MeasurableSet T)
    (hTΓ : ∀ (c : ideleRational F) (x : Points F 1), (c : Points F 1) * x ∈ T ↔ x ∈ T) :
    ideleMeasure F (ideleDomain F ∩ (fun x => normScale F y * x) ⁻¹' T) =
      ideleMeasure F (ideleDomain F ∩ T) :=
  measure_inter_preimage_mul_left (ideleRational F) (ideleMeasure F)
    (isFundamentalDomain_ideleDomain F _) (normScale F y) (points_one_mul_comm F _) hT hTΓ

/-! ### The pushforward of `d^×a` by `log |a|` -/

/-- `log |a|` on `𝔸^×`. -/
def logNorm (a : Points F 1) : ℝ := Real.log (detNorm F 1 a)

theorem measurable_logNorm : Measurable (logNorm F) :=
  Real.measurable_log.comp (measurable_detNorm_one F)

theorem logNorm_normScale_mul (y : ℝ) (a : Points F 1) :
    logNorm F (normScale F y * a) = y + logNorm F a := by
  rw [logNorm, logNorm, detNorm_one_mul, detNorm_normScale,
    Real.log_mul (Real.exp_pos y).ne' (UnequalAnalytic.detNorm_pos F a).ne', Real.log_exp]

theorem logNorm_ideleRational_mul (c : ideleRational F) (a : Points F 1) :
    logNorm F ((c : Points F 1) * a) = logNorm F a := by
  rw [logNorm, logNorm, detNorm_ideleRational_mul]

/-- The image of `d^×a` on `D₁` under `log |a|`. -/
def logNormMeasure : Measure ℝ :=
  Measure.map (logNorm F) ((ideleMeasure F).restrict (ideleDomain F))

theorem logNormMeasure_apply {B : Set ℝ} (hB : MeasurableSet B) :
    logNormMeasure F B = ideleMeasure F (ideleDomain F ∩ logNorm F ⁻¹' B) := by
  rw [logNormMeasure, Measure.map_apply (measurable_logNorm F) hB,
    Measure.restrict_apply ((measurable_logNorm F) hB), inter_comm]

theorem logNormMeasure_preimage_add (y : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    logNormMeasure F ((fun x => y + x) ⁻¹' B) = logNormMeasure F B := by
  rw [logNormMeasure_apply F (hB.preimage (measurable_const_add y)), logNormMeasure_apply F hB]
  have h : logNorm F ⁻¹' ((fun x => y + x) ⁻¹' B) =
      (fun x => normScale F y * x) ⁻¹' (logNorm F ⁻¹' B) := by
    ext a
    simp only [mem_preimage, logNorm_normScale_mul]
  rw [h, ideleMeasure_inter_preimage_normScale F y ((measurable_logNorm F) hB) fun c x => by
    simp only [mem_preimage, logNorm_ideleRational_mul]]

instance logNormMeasure_isAddLeftInvariant : (logNormMeasure F).IsAddLeftInvariant := by
  refine ⟨fun y => ?_⟩
  ext B hB
  rw [Measure.map_apply (measurable_const_add y) hB, logNormMeasure_preimage_add F y hB]

theorem logNormMeasure_Ico_zero_one : logNormMeasure F (Ico 0 1) = 1 := by
  rw [logNormMeasure_apply F measurableSet_Ico]
  have h : logNorm F ⁻¹' Ico 0 1 = ideleSlab F := by
    ext a
    have hpos := UnequalAnalytic.detNorm_pos F a
    simp only [logNorm, ideleSlab, mem_preimage, mem_Ico, Real.log_nonneg_iff hpos,
      Real.log_lt_iff_lt_exp hpos]
  rw [h, ideleMeasure_slab]

theorem logNormMeasure_Ico (a : ℝ) : logNormMeasure F (Ico a (a + 1)) = 1 := by
  have h : Ico a (a + 1) = (fun x => -a + x) ⁻¹' Ico 0 1 := by
    ext x
    simp only [mem_Ico, mem_preimage]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [h, logNormMeasure_preimage_add F (-a) measurableSet_Ico, logNormMeasure_Ico_zero_one]

instance logNormMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (logNormMeasure F) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨N, hN⟩ := hK.isBounded.subset_closedBall_lt 0 0
  obtain ⟨m, hm⟩ := exists_nat_gt N
  have hsub : K ⊆ ⋃ k ∈ Finset.range (2 * m + 1), Ico (-(m : ℝ) + k) (-(m : ℝ) + k + 1) := by
    intro x hx
    have hxb := hN.2 hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hxb
    set k : ℕ := ⌊x + m⌋₊ with hk
    have hxm : 0 ≤ x + m := by linarith [hxb.1]
    have hk1 : (k : ℝ) ≤ x + m := Nat.floor_le hxm
    have hk2 : x + m < k + 1 := Nat.lt_floor_add_one _
    refine mem_iUnion₂.2 ⟨k, Finset.mem_range.2 ?_, ?_, ?_⟩
    · have : (k : ℝ) < 2 * m + 1 := by linarith [hxb.2]
      exact_mod_cast this
    · linarith
    · linarith
  calc logNormMeasure F K
      ≤ logNormMeasure F (⋃ k ∈ Finset.range (2 * m + 1),
          Ico (-(m : ℝ) + k) (-(m : ℝ) + k + 1)) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (2 * m + 1),
          logNormMeasure F (Ico (-(m : ℝ) + k) (-(m : ℝ) + k + 1)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ k ∈ Finset.range (2 * m + 1), 1 := by
        refine Finset.sum_congr rfl fun k _ => logNormMeasure_Ico F _
    _ < ⊤ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        exact ENNReal.natCast_lt_top _

/-- **`log |·|` carries `d^×a` on `D₁` to Lebesgue measure.** -/
theorem logNormMeasure_eq_volume : logNormMeasure F = volume := by
  have h := Measure.isAddLeftInvariant_eq_smul_of_regular (logNormMeasure F) volume
  have hc : Measure.addHaarScalarFactor (logNormMeasure F) volume = 1 := by
    have h1 := congrArg (fun m : Measure ℝ => m (Ico 0 1)) h
    simp only [logNormMeasure_Ico_zero_one, Measure.smul_apply, Real.volume_Ico, sub_zero,
      ENNReal.ofReal_one] at h1
    have h2 : (Measure.addHaarScalarFactor (logNormMeasure F) volume : ℝ≥0∞) = 1 := by
      rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h1
      exact h1.symm
    exact_mod_cast h2
  rw [h, hc, one_smul]

/-- The `d^×a`-measure of a norm-defined subset of `D₁` is the Lebesgue measure of the
corresponding set of logarithms. -/
theorem ideleMeasure_logNorm_preimage {B : Set ℝ} (hB : MeasurableSet B) :
    ideleMeasure F (ideleDomain F ∩ logNorm F ⁻¹' B) = volume B := by
  rw [← logNormMeasure_apply F hB, logNormMeasure_eq_volume]

theorem lintegral_logNorm (u : ℝ → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ a in ideleDomain F, u (logNorm F a) ∂ideleMeasure F = ∫⁻ y, u y := by
  rw [← logNormMeasure_eq_volume F, logNormMeasure, lintegral_map hu (measurable_logNorm F)]

theorem integral_logNorm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (u : ℝ → E')
    (hu : AEStronglyMeasurable u volume) :
    ∫ a in ideleDomain F, u (logNorm F a) ∂ideleMeasure F = ∫ y, u y := by
  rw [← logNormMeasure_eq_volume F] at hu ⊢
  rw [logNormMeasure, integral_map (measurable_logNorm F).aemeasurable hu]

theorem integrableOn_logNorm_iff {E' : Type*} [NormedAddCommGroup E'] (u : ℝ → E')
    (hu : AEStronglyMeasurable u volume) :
    IntegrableOn (fun a => u (logNorm F a)) (ideleDomain F) (ideleMeasure F) ↔
      Integrable u volume := by
  rw [← logNormMeasure_eq_volume F] at hu ⊢
  rw [logNormMeasure, integrable_map_measure hu (measurable_logNorm F).aemeasurable]
  rfl

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
