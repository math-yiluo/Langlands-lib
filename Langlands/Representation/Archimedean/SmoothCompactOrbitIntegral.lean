import Langlands.Representation.Archimedean.SmoothOrbitAveraging
import Langlands.Representation.Archimedean.CompactWeightedOrbit
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Compact orbit integrals in the genuine smooth-vector topology -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Manifold NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

universe uA uE uX

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
  {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] (j : C(X, Aˣ)) (w : C(X, ℂ))

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R

omit [CompleteSpace E] [FiniteDimensional ℝ A] in
private theorem exists_finiteWords_factor (L : D →L[ℂ] ℂ) :
    ∃ (J : Finset (List A)) (T : (J → E) →L[ℂ] ℂ), ∀ v, T (finiteWords R J v) = L v := by
  classical
  let p := (normSeminorm ℂ ℂ).comp L.toLinearMap
  have hp : Continuous p := continuous_norm.comp L.continuous
  obtain ⟨S, C, -, hC⟩ := Seminorm.bound_of_continuous
    (withSeminorms_wordSeminormFamily I R) p hp
  let J := insert [] S
  let F := finiteWords R J
  have hF : Function.Injective F := by
    intro v z h
    apply (toSmooth I R).injective
    apply Subtype.ext
    have h₀ := congrFun h (⟨[], Finset.mem_insert_self _ _⟩ : J)
    change derivativeCLM I R [] v = derivativeCLM I R [] z at h₀
    simpa only [derivativeCLM_apply, iteratedLieDerivative_nil] using h₀
  have hbound (v : D) : ‖L v‖ ≤ (C : ℝ) * ‖F v‖ := by
    have hv := Seminorm.le_def.mp hC v
    rw [smul_apply, NNReal.smul_def, smul_eq_mul] at hv
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
    apply Seminorm.finset_sup_apply_le (norm_nonneg _)
    intro s hs
    change ‖derivativeCLM I R s v‖ ≤ ‖F v‖
    exact norm_le_pi_norm (F v) (⟨s, Finset.mem_insert_of_mem hs⟩ : J)
  let e := LinearEquiv.ofInjective F.toLinearMap hF
  let T₀ : F.toLinearMap.range →ₗ[ℂ] ℂ := L.toLinearMap.comp e.symm.toLinearMap
  have hT₀ (y : F.toLinearMap.range) : ‖T₀ y‖ ≤ (C : ℝ) * ‖y‖ := by
    obtain ⟨v, rfl⟩ := e.surjective y
    change ‖L (e.symm (e v))‖ ≤ (C : ℝ) * ‖F v‖
    rw [LinearEquiv.symm_apply_apply]
    exact hbound v
  obtain ⟨T, hT, _⟩ :=
    exists_extension_norm_eq F.toLinearMap.range (T₀.mkContinuous C hT₀)
  refine ⟨J, T, fun v => ?_⟩
  have h := hT (e v)
  change T (F v) = L (e.symm (e v)) at h
  rwa [LinearEquiv.symm_apply_apply] at h

include hR

omit [CompleteSpace E] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
private theorem continuous_weightedSmoothOrbit (v : D) :
    Continuous (fun x => w x • representation I R (j x) v) :=
  w.continuous.smul ((continuous_representation_units R hR).comp
    (j.continuous.prodMk continuous_const))

private theorem integral_finiteWords_mem_closure (v : D) (J : Finset (List A)) :
    (∫ x, w x • finiteWords R J (representation I R (j x) v) ∂μ) ∈
      closure (range (finiteWords R J)) := by
  let F := finiteWords R J
  let S := F.toLinearMap.range.topologicalClosure
  let : IsClosed (S : Set (J → E)) := F.toLinearMap.range.isClosed_topologicalClosure
  let b : X → J → E := fun x => F (w x • representation I R (j x) v)
  have hb : Integrable b μ :=
    (F.continuous.comp (continuous_weightedSmoothOrbit R hR j w v)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : ∫ x, S.mkQL (b x) ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro x
    apply (Submodule.Quotient.mk_eq_zero S).2
    apply Submodule.le_topologicalClosure
    exact ⟨_, rfl⟩
  have hmem : ∫ x, b x ∂μ ∈ S := by
    apply (Submodule.Quotient.mk_eq_zero S).1
    change S.mkQL (∫ x, b x ∂μ) = 0
    rw [← S.mkQL.integral_comp_comm hb]
    exact hzero
  change (∫ x, b x ∂μ) ∈ closure (range F) at hmem
  simpa only [b, F, map_smul] using hmem

/-- A compactly weighted smooth orbit has a smooth integral whose coordinates
are the Bochner integrals of all the genuine Lie words. -/
theorem exists_compactSmoothAverage (v : D) :
    ∃ y : D, ∀ s : List A,
      derivativeCLM I R s y = ∫ x, w x • derivativeCLM I R s (representation I R (j x) v) ∂μ := by
  let Q : List A → E := fun s =>
    ∫ x, w x • derivativeCLM I R s (representation I R (j x) v) ∂μ
  have hQ : Q ∈ closure (range (derivativeCoordinates I R)) := by
    apply mem_closure_of_finite_projections
    intro J
    let F := finiteWords R J
    let b : X → J → E := fun x => F (w x • representation I R (j x) v)
    have hb : Integrable b μ :=
      (F.continuous.comp (continuous_weightedSmoothOrbit R hR j w v)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have heq : (fun i : J => Q i.val) = ∫ x, b x ∂μ := by
      funext i
      change Q i.val = (ContinuousLinearMap.proj (R := ℂ) i) (∫ x, b x ∂μ)
      rw [← (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => E) i).integral_comp_comm hb]
      simp only [b, F, map_smul]
      rfl
    have hrange : (fun z : List A → E => fun i : J => z i.val) '' range (derivativeCoordinates I R) =
        range F := by
      rw [← range_comp]
      rfl
    rw [heq, hrange]
    simpa only [b, F, map_smul] using integral_finiteWords_mem_closure R hR μ j w v J
  rw [(isClosed_range_derivativeCoordinates_units R hR).closure_eq] at hQ
  obtain ⟨y, hy⟩ := hQ
  exact ⟨y, fun s => congrFun hy s⟩

/-- The weighted compact average as a genuine smooth vector. -/
def compactSmoothAverage (v : D) : D :=
  (exists_compactSmoothAverage R hR μ j w v).choose

theorem derivativeCLM_compactSmoothAverage (v : D) (s : List A) :
    derivativeCLM I R s (compactSmoothAverage R hR μ j w v) =
      ∫ x, w x • derivativeCLM I R s (representation I R (j x) v) ∂μ :=
  (exists_compactSmoothAverage R hR μ j w v).choose_spec s

theorem finiteWords_compactSmoothAverage (v : D) (J : Finset (List A)) :
    finiteWords R J (compactSmoothAverage R hR μ j w v) =
      ∫ x, w x • finiteWords R J (representation I R (j x) v) ∂μ := by
  have hf : Continuous (fun x => w x • finiteWords R J (representation I R (j x) v)) := by
    simpa only [Function.comp_def, map_smul] using
      (finiteWords R J).continuous.comp (continuous_weightedSmoothOrbit R hR j w v)
  have hi := hf.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  funext i
  change derivativeCLM I R i.val (compactSmoothAverage R hR μ j w v) =
    (ContinuousLinearMap.proj (R := ℂ) i) (∫ x, w x • finiteWords R J (representation I R (j x) v) ∂μ)
  rw [← (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => E) i).integral_comp_comm hi,
    derivativeCLM_compactSmoothAverage]
  rfl

/-- The empty coordinate agrees with the norm-valued compact Bochner integral. -/
theorem derivativeCLM_nil_compactSmoothAverage (v : D) :
    derivativeCLM I R [] (compactSmoothAverage R hR μ j w v) =
      compactWeightedOrbit μ R hR j w (derivativeCLM I R [] v) := by
  rw [compactWeightedOrbit_apply, derivativeCLM_compactSmoothAverage]
  apply integral_congr_ae
  filter_upwards with x
  simp only [derivativeCLM_apply, iteratedLieDerivative_nil, toSmooth_representation,
    smoothRepresentation_apply]

/-- Continuous linear scalar evaluations commute with compact smooth orbit integration. -/
theorem apply_compactSmoothAverage (v : D) (L : D →L[ℂ] ℂ) :
    L (compactSmoothAverage R hR μ j w v) =
      ∫ x, w x • L (representation I R (j x) v) ∂μ := by
  obtain ⟨J, T, hT⟩ := exists_finiteWords_factor R L
  have hf : Continuous (fun x => w x • finiteWords R J (representation I R (j x) v)) := by
    simpa only [Function.comp_def, map_smul] using
      (finiteWords R J).continuous.comp (continuous_weightedSmoothOrbit R hR j w v)
  have hi := hf.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  rw [← hT, finiteWords_compactSmoothAverage, ← T.integral_comp_comm hi]
  simp only [map_smul, hT]

omit hR in
/-- A compactly weighted smooth orbit integral commutes with the genuine word
coordinates and every continuous linear scalar evaluation. -/
def SmoothCompactOrbitIntegralStatement : Prop :=
  IsContinuousRepresentation R →
    ∀ v : D, ∃ y : D,
      (∀ s : List A, derivativeCLM I R s y =
        ∫ x, w x • derivativeCLM I R s (representation I R (j x) v) ∂μ) ∧
      ∀ L : D →L[ℂ] ℂ, L y = ∫ x, w x • L (representation I R (j x) v) ∂μ

omit hR in
theorem smoothCompactOrbitIntegral : SmoothCompactOrbitIntegralStatement R μ j w :=
  fun h v => ⟨compactSmoothAverage R h μ j w v,
    derivativeCLM_compactSmoothAverage R h μ j w v,
    apply_compactSmoothAverage R h μ j w v⟩

end Langlands.Archimedean.DerivativeSmoothVectors
