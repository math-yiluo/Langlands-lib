import Langlands.Correspondence.ArithmeticFactors

noncomputable section

namespace Langlands.Correspondence

universe uF

open LocalClassField LocalFactor LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The bottom intermediate field imposes no condition on a base Weil element. -/
theorem mem_baseWeilSubgroup (w : Weil.Local.localWeilGroup F) :
    w ∈ weilSubgroup F (baseExtension F) := by
  change Weil.projection (Weil.Local.localResidueDegree F) w ∈
    (⊥ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier)).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_bot]
  exact Subgroup.mem_top _

/-- Rebracket a base Weil element in the bottom-field Weil subgroup. -/
def baseWeilEquiv :
    Weil.Local.localWeilGroup F ≃ₜ* weilSubgroup F (baseExtension F) where
  toMulEquiv :=
    { toFun := fun w => ⟨w, mem_baseWeilSubgroup F w⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

/-- A common-closure family cannot have two different base reciprocity maps. -/
theorem IsBaseReciprocity.candidate_eq
    {e₁ e₂ : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h₁ : IsBaseReciprocity F e₁ eC) (h₂ : IsBaseReciprocity F e₂ eC) :
    e₁ = e₂ := by
  apply ContinuousMulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro w
  apply Units.ext
  exact (h₁ (baseWeilEquiv F w)).symm.trans (h₂ (baseWeilEquiv F w))

/-- Once the base component is identified, any other identification is its equality. -/
theorem IsBaseReciprocity.iff_eq
    {e₀ e : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h₀ : IsBaseReciprocity F e₀ eC) :
    IsBaseReciprocity F e eC ↔ e = e₀ := by
  constructor
  · intro h
    exact h.candidate_eq F h₀
  · rintro rfl
    exact h₀

end Langlands.Correspondence
