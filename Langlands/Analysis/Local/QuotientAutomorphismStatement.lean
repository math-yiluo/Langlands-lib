import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-!
# Scaling a compatible quotient measure by a group automorphism

A continuous automorphism of `G` preserving `H` restricts to `H` and descends
to the actual left quotient `LeftQuotient H`. The statement asserts that every
compatible quotient measure is scaled by the quotient of the actual Haar
moduli of the subgroup restriction and of the ambient automorphism.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG

section Packaging

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The restriction to `H` of a continuous automorphism preserving `H`. -/
def subgroupAutomorphism (H : Subgroup G) (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) : H ≃ₜ* H where
  toFun h := ⟨α h, (hα h).2 h.property⟩
  invFun h := ⟨α.symm h, (hα (α.symm h)).1 (by simpa only [α.apply_symm_apply] using h.property)⟩
  left_inv h := by ext; simp
  right_inv h := by ext; simp
  map_mul' h k := by ext; simp
  continuous_toFun := (α.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (α.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem subgroupAutomorphism_apply (H : Subgroup G) (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) (h : H) :
    ((subgroupAutomorphism H α hα h : H) : G) = α h := rfl

@[simp] theorem subgroupAutomorphism_symm_apply (H : Subgroup G) (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) (h : H) :
    (((subgroupAutomorphism H α hα).symm h : H) : G) = α.symm h := rfl

/-- The homeomorphism of the actual left quotient induced by a continuous
automorphism preserving `H`: the coset `H * g` goes to `H * α g`. -/
def quotientAutomorphism (H : Subgroup G) (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) : LeftQuotient H ≃ₜ LeftQuotient H :=
  Homeomorph.Quotient.congr α.toHomeomorph (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ H ↔ α y * (α x)⁻¹ ∈ H
    rw [← map_inv, ← map_mul, hα])

@[simp] theorem quotientAutomorphism_mk (H : Subgroup G) (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) (g : G) :
    quotientAutomorphism H α hα (Quotient.mk _ g) = Quotient.mk _ (α g) := rfl

@[simp] theorem quotientAutomorphism_symm_mk (H : Subgroup G) (α : G ≃ₜ* G)
    (hα : ∀ x : G, α x ∈ H ↔ x ∈ H) (g : G) :
    (quotientAutomorphism H α hα).symm (Quotient.mk _ g) = Quotient.mk _ (α.symm g) := rfl

end Packaging

/-- For a closed subgroup `H` with supplied regular two-sided Haar measures on
`G` and `H`, every compatible quotient measure `ν` on `LeftQuotient H` and every
continuous automorphism `α` of `G` preserving `H`: with `δG` the Haar modulus of
`α` and `δH` that of its restriction to `H`, the pushforward of `ν` by the
induced quotient homeomorphism is `(δH / δG) • ν`, and pulling back an arbitrary
integrand by the inverse quotient homeomorphism multiplies the Bochner integral
by `δG / δH`. -/
def CompatibleQuotientAutomorphismScaling : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) (μH : Measure H)
    [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
    [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (ν : Measure (LeftQuotient H)), IsCompatible H μG μH ν →
    ∀ (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H),
      haveI : LocallyCompactSpace H := hH.locallyCompactSpace
      let αH : H ≃ₜ* H := subgroupAutomorphism H α hα
      let αQ : LeftQuotient H ≃ₜ LeftQuotient H := quotientAutomorphism H α hα
      let δG : ℝ≥0 := mulEquivHaarChar α
      let δH : ℝ≥0 := mulEquivHaarChar αH
      Measure.map αQ ν = (((δH / δG : ℝ≥0) : ℝ≥0∞)) • ν ∧
        ∀ f : LeftQuotient H → ℂ,
          (∫ q, f (αQ.symm q) ∂ν) = (((δG / δH : ℝ≥0) : ℝ) : ℂ) * ∫ q, f q ∂ν

end Langlands.QuotientIntegration
