import Langlands.Global.ArchimedeanSmoothFamily
import Langlands.Global.ArchimedeanCompactLieOrbitDensityProof

/-! # Density for simultaneous smooth right translates -/

noncomputable section
universe u w
open Filter Topology
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.SmoothFamily

open DerivativeSmoothFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {ι : Type w}

private theorem exists_sum_coordinates {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (ℓ : (ι → E) →L[ℂ] ℂ) :
    ∃ I : Finset ι, ∀ f : ι → E, ℓ f =
      ∑ i ∈ I, (ℓ.comp (ContinuousLinearMap.single ℂ (fun _ : ι => E) i)) (f i) := by
  have hU : ℓ ⁻¹' Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ι → E) :=
    ℓ.continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact Metric.ball_mem_nhds _ zero_lt_one)
  rw [nhds_pi] at hU
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hU
  have hzero (v : ι → E) (hv : ∀ i ∈ I, v i = 0) : ℓ v = 0 := by
    by_contra hne
    have hh : (ℓ v)⁻¹ • v ∈ Set.pi (I : Set ι) t := by
      intro i hi
      rw [Pi.smul_apply, hv i hi, smul_zero]
      exact mem_of_mem_nhds (ht i)
    have hb : dist (ℓ ((ℓ v)⁻¹ • v)) 0 < 1 := Metric.mem_ball.mp (hsub hh)
    simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hne, dist_zero_right,
      norm_one, lt_self_iff_false] at hb
  refine ⟨I, fun f => ?_⟩
  let q : ι → E := ∑ i ∈ I, ContinuousLinearMap.single ℂ (fun _ : ι => E) i (f i)
  have hq : ℓ (f - q) = 0 := by
    apply hzero
    intro i hi
    change f i - q i = 0
    have heq : q i = f i := by
      simp only [q, Finset.sum_apply, ContinuousLinearMap.single_apply]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp
      · intro j _ hji
        exact Pi.single_eq_of_ne (M := fun _ : ι => E) hji.symm (f j)
    rw [heq, sub_self]
  rw [map_sub, sub_eq_zero] at hq
  simpa only [q, map_sum, ContinuousLinearMap.comp_apply] using hq

/-- The scalar coefficient of simultaneous translation is an actual smooth function.
Continuity of the functional reduces it to a finite sum of smooth scalar coefficients. -/
def orbitCoefficient (ℓ : SmoothFamily F n ι →L[ℂ] ℂ) (f : SmoothFamily F n ι) :
    SmoothFunctions F n :=
  ⟨fun g => ℓ (rightRepresentation g f), by
    obtain ⟨I, hI⟩ := exists_sum_coordinates ℓ
    let C (i : ι) := smoothOrbitCoefficient F n
      (ℓ.comp (ContinuousLinearMap.single ℂ (fun _ : ι => DerivativeSmoothFunctions F n) i)) (f i)
    have heq : (fun g => ℓ (rightRepresentation g f)) = (∑ i ∈ I, C i).val := by
      funext g
      rw [hI]
      simp only [Submodule.coe_sum, Finset.sum_apply, C, smoothOrbitCoefficient_apply,
        rightRepresentation_apply]
      rfl
    rw [heq]
    exact (∑ i ∈ I, C i).property⟩

@[simp]
theorem orbitCoefficient_apply (ℓ : SmoothFamily F n ι →L[ℂ] ℂ) (f : SmoothFamily F n ι)
    (g : InfiniteAdelicGL F n) :
    (orbitCoefficient ℓ f).val g = ℓ (rightRepresentation g f) := rfl

/-- A simultaneous translate of a coordinatewise joint-finite family lies in the closure
of any submodule containing its simultaneous compact translates of enveloping derivatives. -/
theorem rightRepresentation_mem_closure (S : Submodule ℂ (SmoothFamily F n ι))
    (f : SmoothFamily F n ι) (hf : ∀ i, IsJointFinite F n (toSmooth F n (f i)))
    (hS : ∀ (k : standardInfiniteCompact F n) (a : EnvelopingAlgebra F n),
      compactRepresentation k (a • f) ∈ S) (g : InfiniteAdelicGL F n) :
    rightRepresentation g f ∈ S.topologicalClosure := by
  apply Langlands.Analysis.mem_topologicalClosure_of_forall_complex_annihilator
  intro ℓ hℓ
  obtain ⟨I, hI⟩ := exists_sum_coordinates ℓ
  let L (i : ι) := ℓ.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => DerivativeSmoothFunctions F n) i)
  let C (i : ι) := smoothOrbitCoefficient F n (L i) (f i)
  let A := orbitCoefficient ℓ f
  have hA : A = ∑ i ∈ I, C i := by
    apply Subtype.ext
    funext x
    rw [show A.val x = ℓ (rightRepresentation x f) from rfl, hI]
    simp only [Submodule.coe_sum, Finset.sum_apply, C, L, smoothOrbitCoefficient_apply,
      rightRepresentation_apply]
    rfl
  have hfinite : IsJointFinite F n A := by
    change A ∈ jointFiniteFunctions F n
    rw [hA]
    exact Submodule.sum_mem _ fun i _ => isJointFinite_smoothOrbitCoefficient F n (L i) (f i) (hf i)
  obtain ⟨k, hgk⟩ := compactComponentCoverage F n g
  have hzero (a : EnvelopingAlgebra F n) : (envelopingAction F n a A).val k.val = 0 := by
    have hz := hℓ _ (hS k a)
    rw [hI] at hz
    rw [hA, map_sum, Submodule.coe_sum, Finset.sum_apply]
    simp only [C, L, envelopingAction_smoothOrbitCoefficient_apply]
    exact hz
  exact analyticMatrixJetUniqueness F n A k.val (jointFiniteAnalyticity F n A hfinite)
    (envelopingZeroJet F n A k.val hzero) g hgk

end Langlands.Global.ArchimedeanGL.SmoothFamily
