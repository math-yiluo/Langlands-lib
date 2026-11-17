import Langlands.Representation.Archimedean.SmoothDerivative
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! # The genuine word-derivative topology on smooth vectors -/

noncomputable section

open scoped Manifold ContDiff Topology NNReal
open Filter Topology

namespace Langlands.Archimedean

universe u𝔤 uH uG uE

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E)) [LieGroup I ∞ G]

/-- A dedicated copy of smooth vectors with the topology of all genuine word derivatives. -/
def DerivativeSmoothVectors := smoothVectors I π

namespace DerivativeSmoothVectors

instance : AddCommGroup (DerivativeSmoothVectors I π) :=
  inferInstanceAs (AddCommGroup (smoothVectors I π))

instance : Module ℂ (DerivativeSmoothVectors I π) :=
  inferInstanceAs (Module ℂ (smoothVectors I π))

instance : Module ℝ (DerivativeSmoothVectors I π) :=
  inferInstanceAs (Module ℝ (smoothVectors I π))

instance : IsScalarTower ℝ ℂ (DerivativeSmoothVectors I π) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (smoothVectors I π))

/-- Retain the published smooth vector while forgetting the new topology. -/
def toSmooth : DerivativeSmoothVectors I π ≃ₗ[ℂ] smoothVectors I π :=
  LinearEquiv.refl ℂ (smoothVectors I π)

/-- All genuine word derivatives of a smooth vector, valued in the original normed space. -/
def derivativeCoordinates : DerivativeSmoothVectors I π →ₗ[ℂ] (List 𝔤 → E) :=
  LinearMap.pi fun Xs => (smoothVectors I π).subtype.comp
    ((smoothIteratedLieDerivative I π Xs).comp (toSmooth I π).toLinearMap)

@[simp]
theorem derivativeCoordinates_apply (v : DerivativeSmoothVectors I π) (Xs : List 𝔤) :
    derivativeCoordinates I π v Xs = iteratedLieDerivative I π Xs (toSmooth I π v) := by
  exact smoothIteratedLieDerivative_apply I π Xs (toSmooth I π v)

theorem derivativeCoordinates_injective : Function.Injective (derivativeCoordinates I π) := by
  intro v w h
  apply (toSmooth I π).injective
  apply Subtype.ext
  simpa using congrFun h []

instance : TopologicalSpace (DerivativeSmoothVectors I π) :=
  TopologicalSpace.induced (derivativeCoordinates I π) inferInstance

theorem isEmbedding_derivativeCoordinates : IsEmbedding (derivativeCoordinates I π) :=
  Function.Injective.isEmbedding_induced (derivativeCoordinates_injective I π)

instance : IsTopologicalAddGroup (DerivativeSmoothVectors I π) :=
  (isEmbedding_derivativeCoordinates I π).isInducing.isTopologicalAddGroup
    (derivativeCoordinates I π)

instance : ContinuousSMul ℂ (DerivativeSmoothVectors I π) :=
  continuousSMul_induced (derivativeCoordinates I π)

instance : ContinuousSMul ℝ (DerivativeSmoothVectors I π) :=
  continuousSMul_induced ((derivativeCoordinates I π).restrictScalars ℝ)

instance : T2Space (DerivativeSmoothVectors I π) :=
  (isEmbedding_derivativeCoordinates I π).t2Space

instance : LocallyConvexSpace ℝ (DerivativeSmoothVectors I π) :=
  LocallyConvexSpace.induced ((derivativeCoordinates I π).restrictScalars ℝ)

/-- The continuous linear map selecting one genuine word derivative. -/
def derivativeCLM (Xs : List 𝔤) : DerivativeSmoothVectors I π →L[ℂ] E where
  toLinearMap := (LinearMap.proj Xs).comp (derivativeCoordinates I π)
  cont := (continuous_apply Xs).comp (isEmbedding_derivativeCoordinates I π).continuous

@[simp]
theorem derivativeCLM_apply (Xs : List 𝔤) (v : DerivativeSmoothVectors I π) :
    derivativeCLM I π Xs v = iteratedLieDerivative I π Xs (toSmooth I π v) :=
  derivativeCoordinates_apply I π v Xs

/-- Genuine differentiation on the copy with derivative topology. -/
def operator (X : 𝔤) : DerivativeSmoothVectors I π →ₗ[ℂ] DerivativeSmoothVectors I π :=
  (toSmooth I π).symm.toLinearMap.comp
    ((smoothLieDerivative I π X).comp (toSmooth I π).toLinearMap)

theorem derivativeCoordinates_operator (Xs : List 𝔤) (X : 𝔤)
    (v : DerivativeSmoothVectors I π) :
    derivativeCoordinates I π (operator I π X v) Xs =
      derivativeCoordinates I π v (Xs ++ [X]) := by
  change ((smoothIteratedLieDerivative I π Xs)
    (smoothLieDerivative I π X (toSmooth I π v)) : E) =
    (smoothIteratedLieDerivative I π (Xs ++ [X]) (toSmooth I π v) : E)
  rw [smoothIteratedLieDerivative_append]
  rfl

theorem continuous_operator (X : 𝔤) : Continuous (operator I π X) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro Xs
  change Continuous (fun v => derivativeCoordinates I π (operator I π X v) Xs)
  simp_rw [derivativeCoordinates_operator]
  exact (derivativeCLM I π (Xs ++ [X])).continuous

@[simp]
theorem toSmooth_operator (X : 𝔤) (v : DerivativeSmoothVectors I π) :
    toSmooth I π (operator I π X v) = smoothLieDerivative I π X (toSmooth I π v) :=
  rfl

/-- Each genuine derived operator is continuous for the derivative topology. -/
def operatorCLM (X : 𝔤) : DerivativeSmoothVectors I π →L[ℂ] DerivativeSmoothVectors I π :=
  ⟨operator I π X, continuous_operator I π X⟩

@[simp]
theorem operatorCLM_apply (X : 𝔤) (v : DerivativeSmoothVectors I π) :
    operatorCLM I π X v = operator I π X v :=
  rfl

/-- Convergence means convergence in the original norm of every genuine word derivative. -/
theorem tendsto_iff_derivativeCoordinates {ι : Type*} {l : Filter ι}
    {f : ι → DerivativeSmoothVectors I π} {v : DerivativeSmoothVectors I π} :
    Tendsto f l (𝓝 v) ↔ ∀ Xs, Tendsto
      (fun i => iteratedLieDerivative I π Xs (toSmooth I π (f i))) l
      (𝓝 (iteratedLieDerivative I π Xs (toSmooth I π v))) := by
  rw [(isEmbedding_derivativeCoordinates I π).tendsto_nhds_iff, tendsto_pi_nhds]
  simp only [Function.comp_apply, derivativeCoordinates_apply]

/-- The genuine word seminorms, transported to the dedicated copy. -/
def wordSeminormFamily : SeminormFamily ℂ (DerivativeSmoothVectors I π) (List 𝔤) :=
  fun Xs => (wordSeminorm I π Xs).comp (toSmooth I π).toLinearMap

@[simp]
theorem wordSeminormFamily_apply (Xs : List 𝔤) (v : DerivativeSmoothVectors I π) :
    wordSeminormFamily I π Xs v = ‖iteratedLieDerivative I π Xs (toSmooth I π v)‖ :=
  wordSeminorm_apply I π Xs (toSmooth I π v)

/-- The derivative topology is exactly the topology of the genuine word seminorms. -/
theorem withSeminorms_wordSeminormFamily : WithSeminorms (wordSeminormFamily I π) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf,
    (isEmbedding_derivativeCoordinates I π).isInducing.nhds_eq_comap, map_zero, nhds_pi,
    Filter.pi, Filter.comap_iInf]
  refine iInf_congr fun Xs => ?_
  rw [Pi.zero_apply, ← comap_norm_nhds_zero, Filter.comap_comap, Filter.comap_comap]
  congr 1

end DerivativeSmoothVectors

/-- The published finite-word bound implies continuity for the genuine derivative topology. -/
theorem continuous_of_isContinuousOnSmoothVectors
    (L : smoothVectors I π →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L) :
    Continuous (fun v : DerivativeSmoothVectors I π =>
      L (DerivativeSmoothVectors.toSmooth I π v)) := by
  obtain ⟨S, C, hL⟩ := hL
  let L' := L.comp (DerivativeSmoothVectors.toSmooth I π).toLinearMap
  change Continuous L'
  apply continuous_of_tendsto_nhds_zero L'
  apply squeeze_zero_norm (fun v => hL (DerivativeSmoothVectors.toSmooth I π v))
  have hc : Continuous (fun v : DerivativeSmoothVectors I π =>
      C * ∑ Xs ∈ S, ‖DerivativeSmoothVectors.derivativeCLM I π Xs v‖) :=
    continuous_const.mul (continuous_finsetSum S fun Xs _ =>
      (DerivativeSmoothVectors.derivativeCLM I π Xs).continuous.norm)
  simpa only [map_zero, norm_zero, Finset.sum_const_zero, mul_zero,
    DerivativeSmoothVectors.derivativeCLM_apply] using hc.tendsto 0

/-- Conversely, continuity on the dedicated copy gives the published finite-word bound. -/
theorem isContinuousOnSmoothVectors_of_continuous
    (L : smoothVectors I π →ₗ[ℂ] ℂ)
    (hL : Continuous (fun v : DerivativeSmoothVectors I π =>
      L (DerivativeSmoothVectors.toSmooth I π v))) :
    IsContinuousOnSmoothVectors I π L := by
  classical
  let e := DerivativeSmoothVectors.toSmooth I π
  let q : Seminorm ℂ (DerivativeSmoothVectors I π) :=
    (normSeminorm ℂ ℂ).comp (L.comp e.toLinearMap)
  have hq : Continuous q := continuous_norm.comp hL
  obtain ⟨S, C, -, hC⟩ := Seminorm.bound_of_continuous
    (DerivativeSmoothVectors.withSeminorms_wordSeminormFamily I π) q hq
  refine ⟨S, C, fun v => ?_⟩
  have h₁ : ‖L v‖ ≤ (C : ℝ) * (S.sup (DerivativeSmoothVectors.wordSeminormFamily I π))
      (e.symm v) := by
    have h := Seminorm.le_def.mp hC (e.symm v)
    rw [smul_apply, NNReal.smul_def, smul_eq_mul] at h
    simpa [q, e] using h
  refine h₁.trans (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
  refine Seminorm.finset_sup_apply_le
    (Finset.sum_nonneg fun Xs _ => norm_nonneg _) fun Xs hXs => ?_
  rw [DerivativeSmoothVectors.wordSeminormFamily_apply, LinearEquiv.apply_symm_apply]
  exact Finset.single_le_sum (f := fun Xs => ‖iteratedLieDerivative I π Xs v‖)
    (fun Xs _ => norm_nonneg _) hXs

/-- The published finite-word continuity predicate is exactly continuity on the
dedicated copy with the genuine derivative topology. -/
theorem continuous_iff_isContinuousOnSmoothVectors (L : smoothVectors I π →ₗ[ℂ] ℂ) :
    Continuous (fun v : DerivativeSmoothVectors I π =>
      L (DerivativeSmoothVectors.toSmooth I π v)) ↔ IsContinuousOnSmoothVectors I π L :=
  ⟨isContinuousOnSmoothVectors_of_continuous I π L,
    continuous_of_isContinuousOnSmoothVectors I π L⟩

/-- Hahn--Banach extends a functional with the same finite genuine word bound.
This asserts existence, with no uniqueness, density or equivariance conclusion. -/
theorem exists_extension_of_word_bound (V : Submodule ℂ (smoothVectors I π))
    (ℓ : V →ₗ[ℂ] ℂ) (S : Finset (List 𝔤)) (C : ℝ) (hC : 0 ≤ C)
    (hℓ : ∀ v : V, ‖ℓ v‖ ≤ C * ∑ Xs ∈ S,
      ‖iteratedLieDerivative I π Xs (v : smoothVectors I π)‖) :
    ∃ L : smoothVectors I π →ₗ[ℂ] ℂ,
      (∀ v : V, L v = ℓ v) ∧
      (∀ v, ‖L v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖) ∧
      IsContinuousOnSmoothVectors I π L := by
  classical
  let c : NNReal := ⟨C, hC⟩
  let p : Seminorm ℂ (smoothVectors I π) :=
    c • ∑ Xs ∈ S, wordSeminorm I π Xs
  have hp (v : smoothVectors I π) :
      p v = C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖ := by
    simp only [p, smul_apply, NNReal.smul_def, smul_eq_mul, FunLike.coe_sum,
      Finset.sum_apply, wordSeminorm_apply]
    rfl
  obtain ⟨L, hL, hLp⟩ := Module.Dual.exists_extension_of_le_seminorm V ℓ
    (p := p) (fun v => by simpa only [hp] using hℓ v)
  have hb : ∀ v, ‖L v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖ := by
    simpa only [hp] using hLp
  exact ⟨L, hL, hb, S, C, hb⟩

end Langlands.Archimedean
