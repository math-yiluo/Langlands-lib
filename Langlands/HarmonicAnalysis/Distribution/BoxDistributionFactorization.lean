import Langlands.HarmonicAnalysis.Distribution.IntervalTestPrimitive
import Langlands.HarmonicAnalysis.Distribution.LinearTestCoordinates
import Langlands.HarmonicAnalysis.Distribution.ProductFiberIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! # Factoring a distribution through integration over rectangular coordinates -/

noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Opens E} {a b : ℝ}

/-- The open box with every coordinate in the same real interval. -/
def openIntervalBox (d : ℕ) (a b : ℝ) : Opens (Fin d → ℝ) :=
  ⟨univ.pi (fun _ => Ioo a b), isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)⟩

@[simp]
theorem mem_openIntervalBox {d : ℕ} {v : Fin d → ℝ} :
    v ∈ openIntervalBox d a b ↔ ∀ i, v i ∈ Ioo a b := by
  change v ∈ univ.pi (fun _ => Ioo a b) ↔ _
  simp [mem_pi]

private def splitFirstCoordinate (d : ℕ) : (Fin (d + 1) → ℝ) ≃L[ℝ] ℝ × (Fin d → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.consEquiv (fun _ : Fin (d + 1) => ℝ)).symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private def insertFirstCoordinate (d : ℕ) :
    ((E × (Fin d → ℝ)) × ℝ) ≃L[ℝ] E × (Fin (d + 1) → ℝ) :=
  (ContinuousLinearEquiv.prodAssoc ℝ E (Fin d → ℝ) ℝ).trans
    ((ContinuousLinearEquiv.refl ℝ E).prodCongr
      ((ContinuousLinearEquiv.prodComm ℝ (Fin d → ℝ) ℝ).trans (splitFirstCoordinate d).symm))

private theorem insertFirstCoordinate_apply (d : ℕ) (x : E) (w : Fin d → ℝ) (r : ℝ) :
    insertFirstCoordinate d ((x, w), r) = (x, Fin.cons r w) := rfl

private theorem preimage_insertFirstCoordinate (d : ℕ) :
    (insertFirstCoordinate (E := E) d) ⁻¹'
        (productTestDomain U (openIntervalBox (d + 1) a b) : Set _) =
      (productTestDomain (productTestDomain U (openIntervalBox d a b))
        (intervalTestDomain a b) : Set _) := by
  ext ⟨⟨x, w⟩, r⟩
  change (x, Fin.cons r w) ∈ productTestDomain U (openIntervalBox (d + 1) a b) ↔
    ((x, w), r) ∈ productTestDomain (productTestDomain U (openIntervalBox d a b))
      (intervalTestDomain a b)
  simp only [mem_productTestDomain, mem_openIntervalBox]
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact ⟨fun ⟨hx, hr, hw⟩ => ⟨⟨hx, hw⟩, hr⟩, fun ⟨⟨hx, hw⟩, hr⟩ => ⟨hx, hr, hw⟩⟩

private theorem preimage_insertFirstCoordinate_symm (d : ℕ) :
    (insertFirstCoordinate (E := E) d).symm ⁻¹'
        (productTestDomain (productTestDomain U (openIntervalBox d a b))
          (intervalTestDomain a b) : Set _) =
      (productTestDomain U (openIntervalBox (d + 1) a b) : Set _) := by
  rw [← preimage_insertFirstCoordinate (U := U) (a := a) (b := b) d, ← preimage_comp]
  simp

private theorem intervalProductTestCLM_lineDerivCLM (χ : 𝓓(intervalTestDomain a b, ℝ))
    (f : 𝓓(U, ℝ)) (v : E) :
    intervalProductTestCLM χ (TestFunction.lineDerivCLM ℝ v f) =
      TestFunction.lineDerivCLM ℝ (v, 0) (intervalProductTestCLM χ f) := by
  ext p
  rw [intervalProductTestCLM_apply, lineDerivCLM_smoothTest_apply, lineDerivCLM_smoothTest_apply]
  have hχ := (χ.contDiff.differentiable (by simp) p.2).hasFDerivAt.comp p
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hf := (f.contDiff.differentiable (by simp) p.1).hasFDerivAt.comp p
    (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
  change χ p.2 • fderiv ℝ f p.1 v =
    fderiv ℝ (((χ : ℝ → ℝ) ∘ Prod.snd) * ((f : E → ℝ) ∘ Prod.fst)) p (v, 0)
  rw [(hχ.mul hf).fderiv]
  simp [smul_eq_mul]

private theorem integral_fin_cons {d : ℕ} (f : (Fin (d + 1) → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ t, f t) = ∫ w : Fin d → ℝ, ∫ r : ℝ, f (Fin.cons r w) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
  have hmp : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm _
  have hcons (p : ℝ × (Fin d → ℝ)) : e p = Fin.cons p.1 p.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [← hmp.integral_comp' f]
  have hfi := hmp.integrable_comp_of_integrable hf
  rw [Measure.volume_eq_prod] at hfi ⊢
  change (∫ z, (f ∘ e) z ∂volume.prod volume) = _
  rw [integral_prod_symm _ hfi]
  simp only [comp_apply, hcons]

private theorem integrable_productTest_slice {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasureSpace W] [BorelSpace W]
    [IsFiniteMeasureOnCompacts (volume : Measure W)] {V : Opens W}
    (f : 𝓓(productTestDomain U V, ℝ)) (x : E) :
    Integrable (fun t : W => f (x, t)) := by
  apply (f.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (f.hasCompactSupport.image continuous_snd)
  intro y hy
  exact ⟨(x, y), subset_tsupport f hy, rfl⟩

private theorem exists_intervalTest_integral_one (hab : a < b) :
    ∃ χ : 𝓓(intervalTestDomain a b, ℝ), (∫ r in a..b, χ r) = 1 := by
  obtain ⟨x, hx, hxb⟩ := exists_between hab
  obtain ⟨χ, _, hχ⟩ :=
    exists_normalized_smoothTest (V := intervalTestDomain a b) volume (x := x) ⟨hx, hxb⟩
  refine ⟨χ, ?_⟩
  rw [intervalIntegral.integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero, hχ]
  intro r hr
  exact χ.zero_on_compl fun hm => hr ⟨hm.1, hm.2.le⟩

/-- A functional killing all constant derivatives in the box variables
annihilates every test with zero box integral at each parameter value. -/
theorem eval_eq_zero_of_boxIntegrals_eq_zero (d : ℕ) (hab : a < b)
    (T : 𝓓(productTestDomain U (openIntervalBox d a b), ℝ) →L[ℝ] F)
    (hT : ∀ (v : Fin d → ℝ) (f : 𝓓(productTestDomain U (openIntervalBox d a b), ℝ)),
      T (TestFunction.lineDerivCLM ℝ (0, v) f) = 0)
    (f : 𝓓(productTestDomain U (openIntervalBox d a b), ℝ))
    (hf : ∀ x, (∫ t : Fin d → ℝ, f (x, t)) = 0) : T f = 0 := by
  induction d with
  | zero =>
    have hz : f = 0 := by
      ext p
      have h := hf p.1
      rw [Measure.volume_pi_eq_dirac p.2, integral_dirac] at h
      exact h
    rw [hz, map_zero]
  | succ d ih =>
    let k : ((E × (Fin d → ℝ)) × ℝ) ≃L[ℝ] E × (Fin (d + 1) → ℝ) :=
      insertFirstCoordinate d
    let pull := openLinearTestPullbackCLM k (preimage_insertFirstCoordinate (U := U) (a := a) (b := b) d)
    let push := openLinearTestPullbackCLM k.symm
      (preimage_insertFirstCoordinate_symm (U := U) (a := a) (b := b) d)
    let T' := T.comp push
    have hpush : push (pull f) = f := by
      ext p
      simp [push, pull]
    have hT' (w : Fin d → ℝ) (r : ℝ)
        (φ : 𝓓(productTestDomain (productTestDomain U (openIntervalBox d a b))
          (intervalTestDomain a b), ℝ)) :
        T' (TestFunction.lineDerivCLM ℝ ((0, w), r) φ) = 0 := by
      have h := openLinearTestPullbackCLM_lineDerivCLM k.symm
        (preimage_insertFirstCoordinate_symm (U := U) (a := a) (b := b) d) φ
        (0, Fin.cons r w)
      have hk : k.symm (0, Fin.cons r w) = ((0, w), r) := by
        change k.symm (k ((0, w), r)) = _
        exact k.symm_apply_apply _
      rw [hk] at h
      change T (push (TestFunction.lineDerivCLM ℝ ((0, w), r) φ)) = 0
      rw [h]
      exact hT (Fin.cons r w) (push φ)
    obtain ⟨χ, hχ⟩ := exists_intervalTest_integral_one hab
    rw [← hpush]
    change T' (pull f) = 0
    rw [eval_eq_of_annihilates_intervalDerivatives hab T' (hT' 0 1) χ hχ]
    apply ih
    · intro v φ
      change T' (intervalProductTestCLM χ (TestFunction.lineDerivCLM ℝ (0, v) φ)) = 0
      rw [intervalProductTestCLM_lineDerivCLM]
      exact hT' v 0 _
    · intro x
      have hslice (w : Fin d → ℝ) :
          intervalSliceTest hab.le (pull f) (x, w) = ∫ r : ℝ, f (x, Fin.cons r w) := by
        simp only [intervalSliceTest_apply, pull, openLinearTestPullbackCLM_apply]
        change (∫ r in a..b, f (x, Fin.cons r w)) = _
        rw [intervalIntegral.integral_of_le hab.le]
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro r hr
        apply f.zero_on_compl
        intro hp
        have hm := mem_openIntervalBox.mp (mem_productTestDomain.mp hp).2 (0 : Fin (d + 1))
        exact hr ⟨by simpa using hm.1, by simpa using hm.2.le⟩
      simp_rw [hslice]
      rw [← integral_fin_cons _ (integrable_productTest_slice f x)]
      exact hf x

/-- The continuous functional factors through the box integral, with its
parameter functional obtained by inserting any scalar test of integral one. -/
theorem eval_eq_of_annihilates_boxDerivatives (d : ℕ) (hab : a < b)
    (T : 𝓓(productTestDomain U (openIntervalBox d a b), ℝ) →L[ℝ] F)
    (hT : ∀ (v : Fin d → ℝ) (f : 𝓓(productTestDomain U (openIntervalBox d a b), ℝ)),
      T (TestFunction.lineDerivCLM ℝ (0, v) f) = 0)
    (χ : 𝓓(openIntervalBox d a b, ℝ)) (hχ : (∫ t, χ t) = 1)
    (f : 𝓓(productTestDomain U (openIntervalBox d a b), ℝ)) :
    T f = (T.comp (productKernelTestCLM (TestFunction.postcompCLM
      (ContinuousLinearMap.mul ℝ ℝ) χ))) (productFiberIntegralTest volume f) := by
  let push : 𝓓(U, ℝ) →L[ℝ] 𝓓(productTestDomain U (openIntervalBox d a b), ℝ) :=
    productKernelTestCLM (TestFunction.postcompCLM (ContinuousLinearMap.mul ℝ ℝ) χ)
  let g := push (productFiberIntegralTest volume f)
  have h := eval_eq_zero_of_boxIntegrals_eq_zero d hab T hT (f - g) ?_
  · rw [map_sub, sub_eq_zero] at h
    exact h
  · intro x
    change (∫ t, f (x, t) - g (x, t)) = 0
    rw [integral_sub (integrable_productTest_slice f x) (integrable_productTest_slice g x)]
    have hg (t : Fin d → ℝ) : g (x, t) = χ t * (∫ q, f (x, q)) := rfl
    simp_rw [hg, integral_mul_const, hχ, one_mul, sub_self]

end Langlands.HarmonicAnalysis
