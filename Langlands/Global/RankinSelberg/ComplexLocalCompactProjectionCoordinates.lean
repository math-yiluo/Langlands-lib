import Langlands.Global.RankinSelberg.ComplexLocalCompactProjection
import Langlands.Analysis.CompactWeightedIntegral

/-! # Compact projection coordinates independent of the inducing vector -/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

section Evaluation

variable {K E : Type*} [AddCommGroup E] [Module ℂ E]

variable [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Integration of an orbit with finite span can be computed by every
linear functional on the ambient vector space, using its finite coordinates. -/
theorem exists_compact_average_vector
    (ν : Measure K) [IsFiniteMeasure ν] (κ : K → ℂ) (hκ : Continuous κ)
    (ρ : E →ₗ[ℂ] (K → ℂ)) (hρ : Function.Injective ρ)
    (v : K → E) (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)))
    (hcont : ∀ x, Continuous fun k => ρ (v k) x) :
    ∃ p : E, ∀ ℓ : E →ₗ[ℂ] ℂ, ℓ p = ∫ k, κ k * ℓ (v k) ∂ν := by
  classical
  let V := Submodule.span ℂ (Set.range v)
  let : FiniteDimensional ℂ V := hfin
  let v' (k : K) : V := ⟨v k, Submodule.subset_span ⟨k, rfl⟩⟩
  let b := Module.finBasis ℂ V
  let u (i : Fin (Module.finrank ℂ V)) (k : K) := b.coord i (v' k)
  have hu (i : Fin (Module.finrank ℂ V)) : Continuous (u i) := by
    obtain ⟨c, hc⟩ :=
      linearForm_eq_finitelyManyEvaluations (ρ.comp V.subtype) (hρ.comp Subtype.val_injective) (b.coord i)
    have heq : u i = fun k => ∑ x ∈ c.support, c x * ρ (v k) x :=
      funext fun k => hc (v' k)
    rw [heq]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hcont x)
  refine ⟨∑ i, (∫ k, κ k * u i k ∂ν) • (b i).val, fun ℓ => ?_⟩
  have hv (k : K) : v k = ∑ i, u i k • (b i).val := by
    have h := congrArg Subtype.val (b.sum_repr (v' k))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, ← Module.Basis.coord_apply, u, v'] using h.symm
  symm
  have hsum (k : K) : κ k * ℓ (v k) = ∑ i, κ k * u i k * ℓ (b i).val := by
    rw [hv k, map_sum, Finset.mul_sum]
    simp only [map_smul, smul_eq_mul, mul_assoc]
  simp_rw [hsum]
  rw [integral_finsetSum]
  · simp only [integral_mul_const, map_sum, map_smul, smul_eq_mul]
  · intro i _
    exact ((hκ.mul (hu i)).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Evaluation

section Compact

variable {K G E : Type*}
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [Group G] [AddCommGroup E] [Module ℂ E]

/-- A fixed functional on compactly projected vectors can be expressed by a
single compact pairing whose weight is independent of the original vector
and its group translate. -/
theorem exists_compact_projection_weight
    (ν : Measure K) [ν.IsHaarMeasure] (i : K →* G)
    (κ : K → ℂ) (hκ : Continuous κ)
    (hfin : HasFiniteCompactConvolutionKernel κ)
    (ρ : E →ₗ[ℂ] (K → ℂ)) (hρ : Function.Injective ρ)
    (F : E → G → ℂ) (hF : ∀ v g, Continuous fun k => F v (i k * g))
    (p : E → G → E)
    (hp : ∀ v g x, ρ (p v g) x = ∫ k, κ k * F v (i x * i k * g) ∂ν)
    (ℓ : E →ₗ[ℂ] ℂ) :
    ∃ ω : K → ℂ, Continuous ω ∧ ∀ v g, ℓ (p v g) = ∫ k, ω k * F v (i k * g) ∂ν := by
  classical
  obtain ⟨d, α, β, hβ, hExp⟩ := hfin
  have hshift (v : E) (g : G) (x : K) :
      ρ (p v g) x = ∫ k, κ (x⁻¹ * k) * F v (i k * g) ∂ν := by
    rw [hp, ← integral_mul_left_eq_self (fun k : K => κ (x⁻¹ * k) * F v (i k * g)) x]
    simp only [inv_mul_cancel_left, map_mul]
  let W := Submodule.span ℂ (Set.range α)
  let V := W.comap ρ
  have hV (v : E) (g : G) : p v g ∈ V := by
    change ρ (p v g) ∈ W
    have hsum : ρ (p v g) = ∑ j, (∫ k, β j k * F v (i k * g) ∂ν) • α j := by
      funext x
      rw [hshift]
      simp_rw [hExp, Finset.sum_mul]
      rw [integral_finsetSum]
      · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [mul_assoc, integral_const_mul]
        exact mul_comm _ _
      · intro j _
        exact ((continuous_const.mul (hβ j)).mul (hF v g)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [hsum]
    exact W.sum_mem fun j _ => W.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  let ρW := (ρ.comp V.subtype).codRestrict W (fun v => v.2)
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range α)
  let : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective ρW fun _ _ h => Subtype.ext (hρ (congrArg Subtype.val h))
  obtain ⟨c, hc⟩ :=
    linearForm_eq_finitelyManyEvaluations (ρ.comp V.subtype) (hρ.comp Subtype.val_injective) (ℓ.comp V.subtype)
  let ω (k : K) := ∑ x ∈ c.support, c x * κ (x⁻¹ * k)
  refine ⟨ω, continuous_finsetSum _ fun x _ =>
    continuous_const.mul (hκ.comp (continuous_const.mul continuous_id)), fun v g => ?_⟩
  have h := hc ⟨p v g, hV v g⟩
  change ℓ (p v g) = ∑ x ∈ c.support, c x * ρ (p v g) x at h
  rw [h]
  simp_rw [hshift]
  unfold ω
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun x _ => by simp only [mul_assoc, integral_const_mul]
  · intro x _
    exact ((continuous_const.mul (hκ.comp (continuous_const.mul continuous_id))).mul
      (hF v g)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end Compact

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
