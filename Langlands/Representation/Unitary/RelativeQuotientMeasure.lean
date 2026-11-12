import Langlands.Representation.Induction.CompactQuotientDuality
import Langlands.Representation.Unitary.RelativeHalfModulus

/-! # A relative-modulus integral for a compact homogeneous quotient -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal ENNReal

namespace Langlands.Induction

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- A positive integral, invariant under right translation on functions covariant
under the relative modulus, for a closed subgroup with compact quotient. -/
theorem exists_compactQuotient_relativeMeasure (P : Subgroup G)
    (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
    [CompactSpace (LeftQuotient P)] :
    ∃ μ : Measure (⊤ : Subgroup G),
      (∀ U : Set (⊤ : Subgroup G), IsOpen U →
        (1 : (⊤ : Subgroup G)) ∈ U → 0 < μ U) ∧
      ∀ φ : G → ℂ, IsLocallyConstant φ →
        (∀ (q : P) (x : G), φ ((q : G) * x) =
          (((relativePositiveModulus P q : ℝ≥0) : ℝ) : ℂ) * φ x) →
        ∀ g : G, Integrable (fun k : (⊤ : Subgroup G) => φ ((k : G) * g)) μ ∧
          (∫ k : (⊤ : Subgroup G), φ ((k : G) * g) ∂μ) =
            ∫ k : (⊤ : Subgroup G), φ (k : G) ∂μ := by
  obtain ⟨β₁, β₂, W, hβ₁c, hβ₁s, hβ₂c, hβ₂s, hβ₂0, hWo, hW1, hW, hA, hB⟩ :=
    exists_bruhat_functions P hP
  let Δ : G → ℝ := fun x => (modularCharacter x : ℝ)
  have hΔc : Continuous Δ := NNReal.continuous_coe.comp Haar.continuous_modularCharacter
  have hΔpos : ∀ x : G, 0 < Δ x :=
    fun x => NNReal.coe_pos.mpr (modularCharacterFun_pos x)
  let ρ : G → ℝ := fun x => β₂ x * Δ x
  have hρc : Continuous ρ := hβ₂c.mul hΔc
  have hρs : HasCompactSupport ρ := hβ₂s.mul_right
  have hρ0 : 0 ≤ ρ := fun x => mul_nonneg (hβ₂0 x) (hΔpos x).le
  refine ⟨bruhatMeasure ρ,
    bruhatMeasure_pos ρ hρc.measurable W hWo hW1
      (fun x hx => mul_pos (hW x hx) (hΔpos x)), ?_⟩
  intro φ hφ hcov g
  let ψ : G → ℂ := fun x => (Δ x : ℂ) * φ x
  have hψc : Continuous ψ := (Complex.continuous_ofReal.comp hΔc).mul hφ.continuous
  have hψcov : ∀ (q : P) (x : G),
      ψ ((q : G) * x) = ((modularCharacter q : ℝ) : ℂ) * ψ x := by
    intro q x
    have hn : ((modularCharacter (q : G) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hΔpos q).ne'
    simp [ψ, Δ, hcov, relativePositiveModulus, map_mul,
      mul_assoc, mul_left_comm, mul_comm, hn]
  have key : ∀ g : G,
      ∫ x, (ρ x : ℂ) * φ (x * g) ∂(haar : Measure G) =
        ∫ x, (β₁ x : ℂ) * ψ x ∂(haar : Measure G) := by
    intro g
    have h1 := integral_mul_right_haar
      (fun x : G => (β₂ (x * g⁻¹) : ℂ) * ψ x) g
    have hfun : (fun x : G => (β₂ ((x * g) * g⁻¹) : ℂ) * ψ (x * g)) =
        fun x : G => (Δ g : ℂ) * ((ρ x : ℂ) * φ (x * g)) := by
      funext x
      simp only [mul_inv_cancel_right, ψ, Δ, ρ, map_mul, NNReal.coe_mul,
        Complex.ofReal_mul]
      ring
    rw [hfun, integral_const_mul] at h1
    change (Δ g : ℂ) * _ = (Δ g : ℝ) • _ at h1
    rw [Complex.real_smul] at h1
    rw [mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hΔpos g).ne') h1]
    exact integral_bruhat_eq P hP haar haar (fun p => (modularCharacter p : ℝ))
      (continuous_modularCharacter_of_isClosed P hP) modularCharacter_inv_mul_self
      (fun x => β₂ (x * g⁻¹)) β₁ (hβ₂c.comp (continuous_id.mul continuous_const))
      (hβ₂s.comp_homeomorph (Homeomorph.mulRight g⁻¹)) hβ₁c hβ₁s hA
      (fun x => by simpa only [mul_assoc] using hB (x * g⁻¹)) ψ hψc hψcov
  refine ⟨(integrable_bruhatMeasure_iff ρ hρc.measurable hρ0
    (fun y => φ (y * g))).mpr ?_, ?_⟩
  · exact ((Complex.continuous_ofReal.comp hρc).mul
      (hφ.continuous.comp (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport
      ((hρs.comp_left Complex.ofReal_zero).mul_right)
  · calc
      ∫ k : (⊤ : Subgroup G), φ ((k : G) * g) ∂(bruhatMeasure ρ) =
          ∫ x, (ρ x : ℂ) * φ (x * g) ∂(haar : Measure G) :=
        integral_bruhatMeasure ρ hρc.measurable hρ0 (fun y => φ (y * g))
      _ = ∫ x, (β₁ x : ℂ) * ψ x ∂(haar : Measure G) := key g
      _ = ∫ x, (ρ x : ℂ) * φ (x * 1) ∂(haar : Measure G) := (key 1).symm
      _ = ∫ x, (ρ x : ℂ) * φ x ∂(haar : Measure G) := by simp only [mul_one]
      _ = ∫ k : (⊤ : Subgroup G), φ (k : G) ∂(bruhatMeasure ρ) :=
        (integral_bruhatMeasure ρ hρc.measurable hρ0 φ).symm

/-- A chosen measure realizing the relative-modulus invariant integral. -/
def relativeQuotientMeasure (P : Subgroup G) (hP : IsClosed (P : Set G))
    [LocallyCompactSpace P] [CompactSpace (LeftQuotient P)] :
    Measure (⊤ : Subgroup G) :=
  Classical.choose (exists_compactQuotient_relativeMeasure P hP)

end Langlands.Induction
