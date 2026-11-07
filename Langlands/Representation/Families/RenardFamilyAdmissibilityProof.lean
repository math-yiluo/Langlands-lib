import Langlands.Representation.Families.RenardFamilyFlatnessProof
import Mathlib.Algebra.Module.FinitePresentation

/-! # Admissibility and finite projective fixed modules -/

namespace Langlands.Renard.AlgebraicFamily

universe uB uG uV

/-- Renard VI.8.1 Proposition at all three published universes. -/
theorem admissibilityCriterion : AdmissibilityCriterionStatement.{uB, uG, uV} := by
  intro B _ _ _ _ _ G _ _ _ hG V _ _ ρ hρ
  constructor
  · rintro ⟨hflat, hfinite⟩ K hK
    let := (flatness_iff_fixed_flat hG ρ hρ).mp hflat K hK
    let := hfinite K hK
    let := Module.finitePresentation_of_finite B (fixedVectors ρ K.toSubgroup)
    exact ⟨hfinite K hK, Module.Flat.projective_of_finitePresentation⟩
  · intro hprojective
    refine ⟨(flatness_iff_fixed_flat hG ρ hρ).mpr ?_, fun K hK => (hprojective K hK).1⟩
    intro K hK
    let := (hprojective K hK).2
    infer_instance

end Langlands.Renard.AlgebraicFamily
