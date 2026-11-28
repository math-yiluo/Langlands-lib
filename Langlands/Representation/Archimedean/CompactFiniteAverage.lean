import Langlands.Representation.Archimedean.RealInductionStagesFamily
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Compact averages of algebraically compact-finite vectors -/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean.CompactFiniteAverage

universe uK uV

section

variable {K : Type uK} [Monoid K] [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ K V) (μ : Measure K) [IsFiniteMeasure μ]

private def dualCoordinates : V →ₗ[ℂ] ((Module.Dual ℂ V) → ℂ) where
  toFun v ℓ := ℓ v
  map_add' v w := funext fun ℓ => ℓ.map_add v w
  map_smul' c v := funext fun ℓ => ℓ.map_smul c v

private theorem dual_ext {v w : V} (h : ∀ ℓ : Module.Dual ℂ V, ℓ v = ℓ w) : v = w := by
  apply Module.eval_apply_injective ℂ
  exact LinearMap.ext h

private theorem exists_integral_vector
    (hfinite : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : Module.Dual ℂ V), Continuous (fun k : K => ℓ (ρ k v)))
    (a : C(K, ℂ)) (v : V) :
    ∃ w : V, ∀ ℓ : Module.Dual ℂ V, ℓ w = ∫ k, a k * ℓ (ρ k v) ∂μ := by
  let O := FiniteVectors.orbitSpan ρ v
  let : FiniteDimensional ℂ O := hfinite v
  let J : V →ₗ[ℂ] (Module.Dual ℂ V → ℂ) := dualCoordinates
  let f (k : K) := J (a k • ρ k v)
  have hf (k : K) : f k ∈ O.map J :=
    ⟨a k • ρ k v, O.smul_mem _ (FiniteVectors.action_mem_orbitSpan ρ k v), rfl⟩
  have hi (ℓ : Module.Dual ℂ V) : Integrable (fun k => f k ℓ) μ := by
    have h : Continuous (fun k => a k * ℓ (ρ k v)) := a.continuous.mul (hcont v ℓ)
    simpa only [f, J, dualCoordinates, LinearMap.coe_mk, AddHom.coe_mk, map_smul, Pi.smul_apply, smul_eq_mul] using
      h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm := InductionStages.integral_mem μ (O.map J) hf hi
  obtain ⟨w, _, hw⟩ := hm
  refine ⟨w, fun ℓ => ?_⟩
  have he := congrFun hw ℓ
  change ℓ w = ∫ k, ℓ (a k • ρ k v) ∂μ at he
  simpa only [map_smul, smul_eq_mul] using he

end

/-- Integrating a weighted orbit defines an endomorphism of a compact-finite module
whose scalar orbit functions are continuous. -/
def CompactFiniteAverageStatement : Prop :=
  ∀ (K : Type uK) [Monoid K] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V),
    (∀ v : V, FiniteVectors.IsFiniteVector ρ v) →
    (∀ (v : V) (ℓ : Module.Dual ℂ V), Continuous (fun k : K => ℓ (ρ k v))) →
    ∀ a : C(K, ℂ), ∃ A : Module.End ℂ V,
      ∀ (v : V) (ℓ : Module.Dual ℂ V), ℓ (A v) = ∫ k, a k * ℓ (ρ k v) ∂μ

theorem compactFiniteAverage : CompactFiniteAverageStatement.{uK, uV} := by
  intro K _ _ _ _ _ μ _ V _ _ ρ hfinite hcont a
  classical
  choose A hA using exists_integral_vector ρ μ hfinite hcont a
  refine ⟨{ toFun := A, map_add' := ?_, map_smul' := ?_ }, hA⟩
  · intro v w
    apply dual_ext
    intro ℓ
    rw [map_add, hA, hA, hA]
    simp only [map_add, mul_add]
    exact integral_add
      ((a.continuous.mul (hcont v ℓ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((a.continuous.mul (hcont w ℓ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · intro c v
    apply dual_ext
    intro ℓ
    rw [map_smul, hA, hA, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [map_smul, RingHom.id_apply, smul_eq_mul]
    ring

end Langlands.Archimedean.CompactFiniteAverage
