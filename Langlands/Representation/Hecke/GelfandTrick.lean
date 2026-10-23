import Langlands.Representation.Hecke.Corner
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Gelfand's trick for compact-open Hecke corners -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Hecke

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

include hK in
/-- A continuous automorphism fixing a compact-open subgroup setwise preserves
every regular Haar measure. -/
theorem measurePreserving_of_preimage_eq [LocallyCompactSpace G] [μ.Regular]
    (θ : G ≃ₜ* G) (hθK : θ ⁻¹' (K : Set G) = K) : MeasurePreserving θ μ μ := by
  have hpos : μ (K : Set G) ≠ 0 :=
    (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hfin : μ (K : Set G) ≠ ⊤ := hK.measure_lt_top.ne
  have hc : mulEquivHaarChar θ = 1 := by
    have h := mulEquivHaarChar_smul_preimage μ (X := (K : Set G)) θ
    rw [hθK, ENNReal.smul_def, smul_eq_mul] at h
    have h' : ((mulEquivHaarChar θ : ENNReal)) * μ (K : Set G) = 1 * μ (K : Set G) := by
      rw [h, one_mul]
    rw [ENNReal.mul_left_inj hpos hfin] at h'
    exact_mod_cast h'
  refine ⟨θ.continuous.measurable, ?_⟩
  have h := mulEquivHaarChar_smul_map μ θ
  rwa [hc, one_smul] at h

namespace HeckeAlgebra.Corner

theorem apply_mul_mul (f : Corner μ K hK) (k₁ k₂ : K) (x : G) :
    f ((k₁ : G) * x * (k₂ : G)) = f x := by
  rw [rightInvariant, leftInvariant]

/-- Gelfand's trick: a Haar-measure-preserving automorphism sending every element
into the double coset of its inverse makes the compact-open corner commutative. -/
theorem mul_comm_of_measurePreserving (θ : G ≃ₜ* G) (hθ : MeasurePreserving θ μ μ)
    (hdc : ∀ x : G, ∃ k₁ k₂ : K, θ x = (k₁ : G) * x⁻¹ * (k₂ : G))
    (f g : Corner μ K hK) : f * g = g * f := by
  have hsym : ∀ (h : Corner μ K hK) (z : G), h (θ z) = h z⁻¹ := by
    intro h z
    obtain ⟨k₁, k₂, hz⟩ := hdc z
    rw [hz, apply_mul_mul]
  apply Subtype.ext
  apply HeckeAlgebra.ext
  intro x
  change (f * g) x = (g * f) x
  have h1 : (f * g) x = (f * g) (θ x⁻¹) := by rw [hsym, inv_inv]
  rw [h1, mul_apply, mul_apply]
  calc ∫ y, f y * g (y⁻¹ * θ x⁻¹) ∂μ
      = ∫ u, f (θ u) * g ((θ u)⁻¹ * θ x⁻¹) ∂μ :=
        (hθ.integral_comp θ.toHomeomorph.measurableEmbedding
          (fun y => f y * g (y⁻¹ * θ x⁻¹))).symm
    _ = ∫ u, f u⁻¹ * g (x * u) ∂μ := by
        congr 1
        funext u
        rw [hsym, ← map_inv, ← map_mul, hsym, mul_inv_rev, inv_inv, inv_inv]
    _ = ∫ y, f (y⁻¹ * x) * g y ∂μ := by
        rw [← integral_mul_left_eq_self (fun u => f u⁻¹ * g (x * u)) x⁻¹]
        simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
    _ = ∫ y, g y * f (y⁻¹ * x) ∂μ := by
        simp_rw [mul_comm (f _)]

end HeckeAlgebra.Corner

end Langlands.Hecke
