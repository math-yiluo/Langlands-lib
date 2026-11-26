import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Support

/-! # Continuous reproducing kernels from local `L²` bounds -/

noncomputable section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal NNReal Pointwise Topology

set_option autoImplicit false

namespace Langlands.Analysis

section Evaluation

variable {H : Type*} [TopologicalSpace H] [T2Space H] [One H]
  [MeasurableSpace H] [BorelSpace H]

/-- A bounded evaluation on the restrictions of a space of continuous functions to a compact
set is integration against a measurable `L²` weight supported on that set. -/
private theorem exists_l2_reproducingWeight (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (S : Submodule ℂ (H → ℂ)) (hcont : ∀ f ∈ S, Continuous f)
    (V : Set H) (hV : IsCompact V) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hb : ∀ f ∈ S, ‖f 1‖ₑ ≤ C * eLpNorm f 2 (μ.restrict V)) :
    ∃ k : H → ℂ, Measurable k ∧ MemLp k 2 μ ∧ Function.support k ⊆ V ∧
      ∀ f ∈ S, f 1 = ∫ x, f x * k x ∂μ := by
  classical
  let ν := μ.restrict V
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hV.measure_lt_top.ne
  have hLp (f : S) : MemLp f.val 2 ν := by
    obtain ⟨M, hM⟩ := hV.bddAbove_image (hcont f.val f.property).norm.continuousOn
    exact MemLp.of_bound (hcont f.val f.property).aestronglyMeasurable M
      (ae_restrict_of_forall_mem hV.measurableSet fun x hx => hM ⟨x, hx, rfl⟩)
  let T : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (hLp f).toLp f.val
      map_add' := fun f g => MemLp.toLp_add (hLp f) (hLp g)
      map_smul' := fun c f => MemLp.toLp_const_smul c (hLp f) }
  let ev := (LinearMap.proj (1 : H) : (H → ℂ) →ₗ[ℂ] ℂ).comp S.subtype
  have hb' (f : S) : ‖ev f‖ ≤ C.toReal * ‖T f‖ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC (hLp f).eLpNorm_ne_top) (hb f.val f.property)
    rw [toReal_enorm, ENNReal.toReal_mul, ← Lp.norm_toLp f.val (hLp f)] at h
    exact h
  have hker : LinearMap.ker T ≤ LinearMap.ker ev := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    exact norm_le_zero_iff.mp (by simpa only [hf, norm_zero, mul_zero] using hb' f)
  let L := ((LinearMap.ker T).liftQ ev hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hL (f : S) : L (T.rangeRestrict f) = ev f := by
    have heq : T.quotKerEquivRange ((LinearMap.ker T).mkQ f) = T.rangeRestrict f := Subtype.ext rfl
    change (LinearMap.ker T).liftQ ev hker (T.quotKerEquivRange.symm (T.rangeRestrict f)) = ev f
    rw [← heq, LinearEquiv.symm_apply_apply]
    rfl
  have hLbound (y : LinearMap.range T) : ‖L y‖ ≤ C.toReal * ‖y‖ := by
    obtain ⟨f, hf⟩ := y.property
    have heq : T.rangeRestrict f = y := Subtype.ext hf
    rw [← heq, hL]
    exact hb' f
  obtain ⟨ℓ, hℓ, _⟩ := exists_extension_norm_eq (LinearMap.range T) (L.mkContinuous C.toReal hLbound)
  let v : Lp ℂ 2 ν := (InnerProductSpace.toDual ℂ (Lp ℂ 2 ν)).symm ℓ
  have hinner (f : S) : inner ℂ v (T f) = f.val 1 :=
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := Lp ℂ 2 ν)).trans
      ((hℓ (T.rangeRestrict f)).trans (hL f))
  let k := V.indicator (fun x => conj (v x))
  have hk' : MemLp (fun x => conj (v x)) 2 ν :=
    (Lp.memLp v).of_le (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
      (ae_of_all _ fun x => by simp)
  refine ⟨k, (Complex.continuous_conj.measurable.comp (Lp.stronglyMeasurable v).measurable).indicator
    hV.measurableSet, (memLp_indicator_iff_restrict hV.measurableSet.nullMeasurableSet).mpr hk',
    Set.support_indicator_subset, ?_⟩
  intro f hf
  let u : S := ⟨f, hf⟩
  calc
    f 1 = inner ℂ v (T u) := (hinner u).symm
    _ = ∫ x, f x * conj (v x) ∂ν := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hLp u).coeFn_toLp] with x hx
      change inner ℂ (v x) (T u x) = _
      rw [RCLike.inner_apply, show T u x = f x from hx]
    _ = ∫ x, f x * k x ∂μ := by
      rw [← integral_indicator hV.measurableSet]
      apply congrArg (fun q : H → ℂ => ∫ x, q x ∂μ)
      funext x
      by_cases hx : x ∈ V <;> simp [k, hx]

end Evaluation

section Convolution

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

open scoped InnerProductSpace

/-- The convolution square of a measurable compactly supported `L²` weight is continuous.
It reproduces every continuous function all of whose left translates are reproduced by the
weight. -/
private theorem continuous_reproducingKernel_of_l2_weight (μ : Measure H)
    [μ.IsHaarMeasure] [μ.IsInvInvariant] (V : Set H) (hV : IsCompact V)
    (k : H → ℂ) (hkm : Measurable k) (hk : MemLp k 2 μ) (hkV : Function.support k ⊆ V) :
    ∃ A : H → ℂ, Continuous A ∧ HasCompactSupport A ∧
      ∀ f : H → ℂ, Continuous f → (∀ y, f y = ∫ z, f (y * z) * k z ∂μ) →
        f 1 = ∫ x, f x * A x ∂μ := by
  let A (x : H) := ∫ y, k y * k (y⁻¹ * x) ∂μ
  have hzero {x : H} (hx : x ∉ V) : k x = 0 := Function.notMem_support.mp fun h => hx (hkV h)
  have hkconj : MemLp (fun x => conj (k x)) 2 μ :=
    hk.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hk.aestronglyMeasurable)
      (ae_of_all _ fun x => by simp)
  have hkinv : MemLp (fun x => k x⁻¹) 2 μ := hk.comp_measurePreserving (Measure.measurePreserving_inv μ)
  let p := hkconj.toLp _
  let q := hkinv.toLp _
  let t (x : H) : C(H, H) := ⟨fun y => x⁻¹ * y, continuous_const.mul continuous_id⟩
  have ht : Continuous t := ContinuousMap.continuous_of_continuous_uncurry t (continuous_fst.inv.mul continuous_snd)
  let hmp (x : H) : MeasurePreserving (t x) μ μ := measurePreserving_mul_left μ x⁻¹
  let Q (x : H) := Lp.compMeasurePreserving (t x) (hmp x) q
  have hQ : Continuous Q := continuous_const.compMeasurePreservingLp ht hmp (by norm_num)
  have hAQ (x : H) : A x = inner ℂ p (Q x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hkconj.coeFn_toLp, Lp.coeFn_compMeasurePreserving q (hmp x),
      (hmp x).quasiMeasurePreserving.ae hkinv.coeFn_toLp] with y hp hq hq'
    change k y * k (y⁻¹ * x) = inner ℂ (p y) (Q x y)
    rw [RCLike.inner_apply, hp, hq, Function.comp_apply, hq']
    simp [t, mul_comm]
  have hA : Continuous A := (continuous_const.inner hQ).congr fun x => (hAQ x).symm
  have hAs : HasCompactSupport A := by
    apply HasCompactSupport.of_support_subset_isCompact (hV.mul hV)
    intro x hx
    by_contra hn
    apply hx
    change (∫ y, k y * k (y⁻¹ * x) ∂μ) = 0
    apply integral_eq_zero_of_ae
    refine ae_of_all _ fun y => ?_
    by_cases hy : y ∈ V
    · have hyx : y⁻¹ * x ∉ V := fun hz => hn (by simpa using mul_mem_mul hy hz)
      simp [hzero hyx]
    · simp [hzero hy]
  have hkInt : Integrable k μ := by
    have : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.mpr hV.measure_lt_top.ne
    have h := (hk.restrict V).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have heq : V.indicator k = k := indicator_eq_self.mpr hkV
    rw [← heq]
    exact IntegrableOn.integrable_indicator h hV.measurableSet
  refine ⟨A, hA, hAs, ?_⟩
  intro f hf hrep
  let F (r : H × H) := f (r.1 * r.2) * (k r.1 * k r.2)
  obtain ⟨M, hM⟩ := (hV.mul hV).bddAbove_image hf.norm.continuousOn
  have hF : Integrable F (μ.prod μ) := by
    refine ((hkInt.norm.mul_prod hkInt.norm).const_mul M).mono' ?_ ?_
    · exact (hf.measurable.comp (measurable_fst.mul measurable_snd)).mul
        ((hkm.comp measurable_fst).mul (hkm.comp measurable_snd)) |>.aestronglyMeasurable
    · refine ae_of_all _ fun r => ?_
      rcases r with ⟨y, z⟩
      by_cases hy : y ∈ V
      · by_cases hz : z ∈ V
        · simp only [F, norm_mul]
          exact mul_le_mul_of_nonneg_right (hM ⟨y * z, mul_mem_mul hy hz, rfl⟩) (by positivity)
        · simp [F, hzero hz]
      · simp [F, hzero hy]
  let P (r : H × H) := f r.2 * (k r.1 * k (r.1⁻¹ * r.2))
  have hP (r : H × H) : P r = F (r.1, r.1⁻¹ * r.2) := by simp [P, F]
  have hPi : Integrable P (μ.prod μ) := by
    rw [funext hP]
    exact (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable hF
  have hFubini (y : H) : (∫ z, F (y, z) ∂μ) = f y * k y := by
    rw [hrep y, ← integral_mul_const]
    apply integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp [F]
    ring
  calc
    f 1 = ∫ y, f y * k y ∂μ := by simpa only [one_mul] using hrep 1
    _ = ∫ r, F r ∂(μ.prod μ) := by
      rw [integral_prod _ hF]
      exact integral_congr_ae (ae_of_all _ fun y => (hFubini y).symm)
    _ = ∫ r, P r ∂(μ.prod μ) := by
      rw [funext hP]
      exact ((measurePreserving_prod_inv_mul μ μ).integral_comp
        (MeasurableEquiv.shearMulRight H).symm.measurableEmbedding F).symm
    _ = ∫ x, f x * A x ∂μ := by
      rw [integral_prod_symm _ hPi]
      apply integral_congr_ae (ae_of_all _ fun x => ?_)
      rw [← integral_const_mul]

/-- A single local `L²` bound on evaluation for a left-translation invariant space of continuous
functions yields one continuous compactly supported reproducing kernel for the whole space. -/
theorem exists_compact_reproducingKernel_of_l2_evaluation (μ : Measure H)
    [μ.IsHaarMeasure] [μ.IsInvInvariant] (S : Submodule ℂ (H → ℂ))
    (hcont : ∀ f ∈ S, Continuous f)
    (hleft : ∀ f ∈ S, ∀ y : H, (fun z => f (y * z)) ∈ S)
    (V : Set H) (hV : IsCompact V) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hb : ∀ f ∈ S, ‖f 1‖ₑ ≤ C * eLpNorm f 2 (μ.restrict V)) :
    ∃ A : H → ℂ, Continuous A ∧ HasCompactSupport A ∧
      ∀ f ∈ S, f 1 = ∫ x, f x * A x ∂μ := by
  obtain ⟨k, hkm, hk, hkV, h⟩ := exists_l2_reproducingWeight μ S hcont V hV C hC hb
  obtain ⟨A, hAc, hAs, hA⟩ := continuous_reproducingKernel_of_l2_weight μ V hV k hkm hk hkV
  refine ⟨A, hAc, hAs, fun f hf => hA f (hcont f hf) fun y => ?_⟩
  simpa only [mul_one] using h (fun z => f (y * z)) (hleft f hf y)

end Convolution

end Langlands.Analysis
