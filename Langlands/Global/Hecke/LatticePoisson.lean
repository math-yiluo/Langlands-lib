import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Periodic

/-!
# Poisson summation on `ℤ^ι`

For a continuous function `f : (ι → ℝ) → ℂ` whose translates by `ℤ^ι` are locally uniformly
summable and whose Fourier transform is summable at the integer points,
`∑ n, f (x + n) = ∑ m, 𝓕 f m * e(m · x)`.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace Complex
open scoped Real FourierTransform

namespace Langlands.Global.Hecke

variable {ι : Type*}

/-- An integer vector viewed as a real vector. -/
def intVec (n : ι → ℤ) : ι → ℝ := fun i => (n i : ℝ)

@[simp] lemma intVec_apply (n : ι → ℤ) (i : ι) : intVec n i = (n i : ℝ) := rfl

@[simp] lemma intVec_add (m n : ι → ℤ) : intVec (m + n) = intVec m + intVec n := by
  ext i; simp

variable [Fintype ι]

/-- The dot product of an integer frequency with a real vector. -/
def intDot (m : ι → ℤ) (x : ι → ℝ) : ℝ := ∑ i, (m i : ℝ) * x i

/-- The Fourier transform of `f` on `ι → ℝ` at an integer frequency `m`. -/
def intFourier (f : (ι → ℝ) → ℂ) (m : ι → ℤ) : ℂ :=
  ∫ y, 𝐞 (-intDot m y) • f y

/-- The projection from `ι → ℝ` to the unit torus. -/
def torusMk (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

/-- The projection from `ι → ℝ` to the unit torus, as a continuous map. -/
def torusMkCM : C(ι → ℝ, UnitAddTorus ι) :=
  ⟨torusMk, continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i)⟩

omit [Fintype ι] in
lemma isQuotientMap_torusMk : Topology.IsQuotientMap (torusMkCM (ι := ι)) :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

lemma intDot_intVec (m n : ι → ℤ) : intDot m (intVec n) = ((∑ i, m i * n i : ℤ) : ℝ) := by
  simp [intDot]

lemma fourierChar_intCast (k : ℤ) : 𝐞 (k : ℝ) = 1 := by
  rw [Real.fourierChar_apply']
  have : (2 * π * (k : ℝ)) = (k : ℝ) * (2 * π) := by ring
  rw [this]
  exact Circle.exp_int_mul_two_pi k

lemma mFourier_torusMk (m : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier m (torusMk x) = (𝐞 (intDot m x) : ℂ) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusMk, intDot]
  rw [Real.fourierChar_apply]
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma intDot_neg (m : ι → ℤ) (x : ι → ℝ) : intDot (-m) x = -intDot m x := by
  simp [intDot, Finset.sum_neg_distrib]

lemma intDot_add (m : ι → ℤ) (x y : ι → ℝ) : intDot m (x + y) = intDot m x + intDot m y := by
  simp [intDot, mul_add, Finset.sum_add_distrib]

lemma fourierChar_neg_intDot_add_intVec (m n : ι → ℤ) (x : ι → ℝ) :
    𝐞 (-intDot m (x + intVec n)) = 𝐞 (-intDot m x) := by
  rw [intDot_add, intDot_intVec, neg_add, AddChar.map_add_eq_mul, ← Int.cast_neg,
    fourierChar_intCast, mul_one]

/-! ### The integer lattice and its fundamental domain -/

/-- The half-open unit box `(0, 1]^ι`. -/
def unitBox (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

lemma measurableSet_unitBox : MeasurableSet (unitBox ι) := by
  have : unitBox ι = Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext x; simp [unitBox]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

omit [Fintype ι] in
lemma unitBox_subset_Icc : unitBox ι ⊆ Set.pi univ fun _ => Icc (0 : ℝ) 1 :=
  fun _ hx i _ => Ioc_subset_Icc_self (hx i)

omit [Fintype ι] in
lemma isCompact_Icc_box : IsCompact (Set.pi univ fun _ : ι => Icc (0 : ℝ) 1) :=
  isCompact_univ_pi fun _ => isCompact_Icc

lemma volume_unitBox_lt_top : volume (unitBox ι) < ⊤ :=
  (measure_mono unitBox_subset_Icc).trans_lt isCompact_Icc_box.measure_lt_top

lemma unitBox_ae_eq_fundamentalDomain :
    unitBox ι =ᵐ[volume] ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) := by
  have h1 : unitBox ι = Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext x; simp [unitBox]
  have h2 : ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) = Set.pi univ fun _ => Ico (0 : ℝ) 1 := by
    ext x; simp [ZSpan.mem_fundamentalDomain]
  rw [h1, h2, volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm

lemma intVec_mem_span (n : ι → ℤ) :
    intVec n ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ]
  intro i
  exact ⟨n i, by simp⟩

/-- Integer vectors are the elements of the `ℤ`-span of the standard basis. -/
def intLatticeEquiv : (ι → ℤ) ≃ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup where
  toFun n := ⟨intVec n, intVec_mem_span n⟩
  invFun g := fun i => ⌊(g : ι → ℝ) i⌋
  left_inv n := by ext i; simp
  right_inv g := by
    ext i
    obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (g : ι → ℝ)).mp g.2 i
    simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at hk
    simp [← hk]

instance : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup :=
  intLatticeEquiv.symm.injective.countable

lemma lintegral_eq_tsum_unitBox (h : (ι → ℝ) → ENNReal) :
    ∫⁻ y, h y = ∑' n : ι → ℤ, ∫⁻ x in unitBox ι, h (x + intVec n) := by
  have hF := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  rw [hF.lintegral_eq_tsum']
  rw [← (Equiv.neg _).tsum_eq, ← intLatticeEquiv.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [setLIntegral_congr unitBox_ae_eq_fundamentalDomain]
  congr 1
  ext x
  simp only [Equiv.neg_apply, neg_neg]
  congr 1
  rw [add_comm]
  rfl

lemma integral_eq_tsum_unitBox (h : (ι → ℝ) → ℂ) (hh : Integrable h) :
    ∫ y, h y = ∑' n : ι → ℤ, ∫ x in unitBox ι, h (x + intVec n) := by
  have hF := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  rw [hF.integral_eq_tsum' h hh]
  rw [← (Equiv.neg _).tsum_eq, ← intLatticeEquiv.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [setIntegral_congr_set unitBox_ae_eq_fundamentalDomain]
  congr 1
  ext x
  simp only [Equiv.neg_apply, neg_neg]
  congr 1
  rw [add_comm]
  rfl


/-! ### Periodization and its Fourier coefficients -/

section Periodization

open ContinuousMap

/-- The closed box `[0, 1]^ι` as a compact set. -/
def iccBox (ι : Type*) [Fintype ι] : Compacts (ι → ℝ) := ⟨Icc 0 1, isCompact_Icc⟩

lemma unitBox_subset_iccBox : unitBox ι ⊆ (iccBox ι : Set (ι → ℝ)) :=
  fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

omit [Fintype ι] in
lemma torusMk_eq_torusMk {a b : ι → ℝ} (h : torusMk a = torusMk b) :
    ∃ k : ι → ℤ, b = a + intVec k := by
  have hi : ∀ i, ∃ k : ℤ, b i = a i + k := by
    intro i
    have hab : ((a i : ℝ) : UnitAddCircle) = b i := congr_fun h i
    have h0 : ((b i - a i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, ← hab, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    exact ⟨n, by rw [zsmul_one] at hn; linarith⟩
  choose k hk using hi
  exact ⟨k, funext fun i => by simp [hk i]⟩

variable (f : C(ι → ℝ, ℂ))

/-- The `ℤ^ι`-periodization `x ↦ ∑ n, f (x + n)` of `f`, as a continuous map (it is zero if the
translates of `f` are not summable in `C(ι → ℝ, ℂ)`). -/
def periodization : C(ι → ℝ, ℂ) :=
  ∑' n : ι → ℤ, f.comp (ContinuousMap.addRight (intVec n))

variable {f}

omit [Fintype ι] in
lemma periodization_apply
    (hf : Summable fun n : ι → ℤ => f.comp (ContinuousMap.addRight (intVec n))) (x : ι → ℝ) :
    periodization f x = ∑' n : ι → ℤ, f (x + intVec n) := by
  rw [periodization, ← ContinuousMap.tsum_apply hf]
  rfl

omit [Fintype ι] in
lemma periodization_add_intVec (x : ι → ℝ) (k : ι → ℤ) :
    periodization f (x + intVec k) = periodization f x := by
  by_cases hf : Summable fun n : ι → ℤ => f.comp (ContinuousMap.addRight (intVec n))
  · rw [periodization_apply hf, periodization_apply hf]
    calc ∑' n : ι → ℤ, f (x + intVec k + intVec n)
        = ∑' n : ι → ℤ, f (x + intVec (k + n)) := by simp [add_assoc]
      _ = ∑' n : ι → ℤ, f (x + intVec n) :=
          (Equiv.addLeft k).tsum_eq (fun n => f (x + intVec n))
  · simp [periodization, tsum_eq_zero_of_not_summable hf]

omit [Fintype ι] in
lemma periodization_factorsThrough :
    Function.FactorsThrough (periodization f) (torusMkCM (ι := ι)) := fun a b h => by
  obtain ⟨k, rfl⟩ := torusMk_eq_torusMk h
  exact (periodization_add_intVec a k).symm

variable (f) in
/-- The periodization of `f` as a continuous function on the torus `(ℝ / ℤ)^ι`. -/
def torusPeriodization : C(UnitAddTorus ι, ℂ) :=
  isQuotientMap_torusMk.lift (periodization f) periodization_factorsThrough

omit [Fintype ι] in
lemma torusPeriodization_torusMk (x : ι → ℝ) :
    torusPeriodization f (torusMk x) = periodization f x :=
  DFunLike.congr_fun (isQuotientMap_torusMk.lift_comp (periodization f)
    periodization_factorsThrough) x

lemma norm_fourierChar_smul (t : ℝ) (z : ℂ) : ‖(𝐞 t : ℂ) • z‖ = ‖z‖ := by
  rw [norm_smul, Circle.norm_coe, one_mul]

lemma continuous_fourierChar_neg_intDot (m : ι → ℤ) :
    Continuous fun y : ι → ℝ => (𝐞 (-intDot m y) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)).neg)

/-- If the integer translates of `f` are locally uniformly summable, then `f` is integrable. -/
lemma integrable_of_summable_norm_box
    (hf : Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict (iccBox ι)‖) :
    Integrable f := by
  let s : (ι → ℤ) → Compacts (ι → ℝ) := fun n => ⟨Icc (intVec n) (intVec n + 1), isCompact_Icc⟩
  refine integrable_of_summable_norm_restrict (s := s) (.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg) (fun n => ?_) hf) ?_
  · have hvol : volume.real (s n : Set (ι → ℝ)) = 1 := by
      simp only [s, Compacts.coe_mk, Measure.real]
      rw [Real.volume_Icc_pi_toReal (by intro i; simp)]
      simp
    rw [hvol, mul_one]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x => ?_
    have hx : (x : ι → ℝ) - intVec n ∈ (iccBox ι : Set (ι → ℝ)) := by
      obtain ⟨h1, h2⟩ := x.2
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h1 i; simp only [intVec_apply, Pi.zero_apply, Pi.sub_apply] at this ⊢; linarith
      · have := h2 i
        simp only [intVec_apply, Pi.one_apply, Pi.sub_apply, Pi.add_apply] at this ⊢; linarith
    have := ((f.comp (ContinuousMap.addRight (intVec n))).restrict (iccBox ι)).norm_coe_le_norm
      ⟨_, hx⟩
    simpa only [ContinuousMap.restrict_apply, comp_apply, coe_addRight, sub_add_cancel] using this
  · refine eq_univ_of_forall fun x => mem_iUnion.mpr ⟨fun i => ⌊x i⌋, ?_⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simpa using Int.floor_le (x i)
    · simpa using (Int.lt_floor_add_one (x i)).le

/-- The key lemma for Poisson summation: the Fourier coefficients of the periodization of `f`
are the values of the Fourier transform of `f` at integer points. -/
theorem mFourierCoeff_torusPeriodization
    (hf : ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖) (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization f) m = intFourier f m := by
  have hs := summable_of_locally_summable_norm hf
  have hbox : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} = unitBox ι := by
    ext x; simp [unitBox]
  -- integrability of the summands on the unit box
  have hint : ∀ n : ι → ℤ, IntegrableOn
      (fun x => (𝐞 (-intDot m x) : ℂ) • f (x + intVec n)) (unitBox ι) := by
    intro n
    refine (ContinuousOn.integrableOn_compact (iccBox ι).isCompact ?_).mono_set
      unitBox_subset_iccBox
    exact ((continuous_fourierChar_neg_intDot m).smul
      (f.continuous.comp (continuous_id.add continuous_const))).continuousOn
  have hnorm : ∀ n : ι → ℤ, ∫ x in unitBox ι, ‖(𝐞 (-intDot m x) : ℂ) • f (x + intVec n)‖ ≤
      ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict (iccBox ι)‖ *
        volume.real (unitBox ι) := by
    intro n
    refine le_trans (le_abs_self _) ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const volume_unitBox_lt_top fun x hx => ?_
    rw [norm_norm, norm_fourierChar_smul]
    have := ((f.comp (ContinuousMap.addRight (intVec n))).restrict (iccBox ι)).norm_coe_le_norm
      ⟨x, unitBox_subset_iccBox hx⟩
    simpa only [ContinuousMap.restrict_apply, comp_apply, coe_addRight] using this
  have hintF : Integrable fun y => (𝐞 (-intDot m y) : ℂ) • f y := by
    let g : C(ι → ℝ, ℂ) :=
      ⟨fun y => (𝐞 (-intDot m y) : ℂ) • f y, (continuous_fourierChar_neg_intDot m).smul f.continuous⟩
    have : Integrable g := by
      refine integrable_of_summable_norm_box ((hf (iccBox ι)).congr fun n => ?_)
      rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
      congr 1
      ext x
      change ‖f (x + intVec n)‖ = ‖(𝐞 (-intDot m (x + intVec n)) : ℂ) • f (x + intVec n)‖
      rw [norm_fourierChar_smul]
    exact this
  calc UnitAddTorus.mFourierCoeff (torusPeriodization f) m
      = ∫ x in unitBox ι, (𝐞 (-intDot m x) : ℂ) • ∑' n : ι → ℤ, f (x + intVec n) := by
        rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0, hbox]
        refine setIntegral_congr_fun measurableSet_unitBox fun x _ => ?_
        change UnitAddTorus.mFourier (-m) (torusMk x) • torusPeriodization f (torusMk x) = _
        rw [mFourier_torusMk, torusPeriodization_torusMk, periodization_apply hs, intDot_neg]
    _ = ∫ x in unitBox ι, ∑' n : ι → ℤ, (𝐞 (-intDot m x) : ℂ) • f (x + intVec n) := by
        refine setIntegral_congr_fun measurableSet_unitBox fun x _ => ?_
        rw [tsum_const_smul'' ]
    _ = ∑' n : ι → ℤ, ∫ x in unitBox ι, (𝐞 (-intDot m x) : ℂ) • f (x + intVec n) := by
        refine (integral_tsum_of_summable_integral_norm hint ?_).symm
        refine .of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm ?_
        exact (hf (iccBox ι)).mul_right _
    _ = ∑' n : ι → ℤ, ∫ x in unitBox ι,
          (fun y => (𝐞 (-intDot m y) : ℂ) • f y) (x + intVec n) := by
        refine tsum_congr fun n => setIntegral_congr_fun measurableSet_unitBox fun x _ => ?_
        simp only [fourierChar_neg_intDot_add_intVec]
    _ = intFourier f m := (integral_eq_tsum_unitBox _ hintF).symm

/-- **Poisson summation on `ℤ^ι`**, as a `HasSum` statement: if the integer translates of `f`
are locally uniformly summable and the Fourier transform of `f` is summable on `ℤ^ι`, then the
Fourier series `∑ m, 𝓕 f m * e(m · x)` converges to the periodization `∑ n, f (x + n)`. -/
theorem hasSum_intFourier_mul_fourierChar
    (hf : ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (h_sum : Summable (intFourier f)) (x : ι → ℝ) :
    HasSum (fun m : ι → ℤ => intFourier f m * 𝐞 (intDot m x))
      (∑' n : ι → ℤ, f (x + intVec n)) := by
  have hc : UnitAddTorus.mFourierCoeff (torusPeriodization f) = intFourier f :=
    funext (mFourierCoeff_torusPeriodization hf)
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (hc ▸ h_sum) (torusMk x)
  rw [torusPeriodization_torusMk, periodization_apply (summable_of_locally_summable_norm hf),
    hc] at h
  simpa only [mFourier_torusMk, smul_eq_mul] using h

/-- **Poisson summation on `ℤ^ι`**: if the integer translates of `f` are locally uniformly
summable and the Fourier transform of `f` is summable on `ℤ^ι`, then
`∑ n, f (x + n) = ∑ m, 𝓕 f m * e(m · x)`. -/
theorem tsum_add_intVec_eq_tsum_intFourier
    (hf : ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (h_sum : Summable (intFourier f)) (x : ι → ℝ) :
    ∑' n : ι → ℤ, f (x + intVec n) = ∑' m : ι → ℤ, intFourier f m * 𝐞 (intDot m x) :=
  (hasSum_intFourier_mul_fourierChar hf h_sum x).tsum_eq.symm

end Periodization

end Langlands.Global.Hecke
