import Langlands.LocalFactor.CommonClosure

/-! # Surjectivity of a supplied common-closure reciprocity component -/

noncomputable section

namespace Langlands.LocalFactor.CommonClosure

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The supplied reciprocity component is surjective on units. -/
theorem reciprocityUnits_surjective
    (e : ReciprocityFamily F) (E : Extension F) :
    Function.Surjective (reciprocityUnits F e E) := by
  let := (fieldData F E).topology
  intro z
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective ((e E).symm z)
  refine ⟨x, ?_⟩
  change e E (QuotientGroup.mk x) = z
  rw [hx]
  exact (e E).apply_symm_apply z

end Langlands.LocalFactor.CommonClosure
