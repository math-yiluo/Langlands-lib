import Langlands.Representation.Smooth.CompactDistributionActionStatements

/-! # The left regular distribution action is convolution -/

namespace Langlands

open HarmonicAnalysis

universe u

/-- Evaluation of the scalar characterization gives the left convolution kernel. -/
theorem leftRegularCompactDistribution :
    LeftRegularCompactDistributionStatement.{u} := by
  intro G _ _ _ _ _ _ act hact T f x
  let ev : Module.Dual ℂ (SchwartzBruhat G) :=
    { toFun := fun q => q x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let φ : LocallyConstant G ℂ :=
    ⟨fun g => f (g⁻¹ * x),
      f.locallyConstant.comp_continuous (continuous_inv.mul continuous_const)⟩
  have h := hact T f ev φ (fun _ => rfl)
  change act T f x = Distribution.compactSupportFunctional T φ at h
  rw [h]
  apply Distribution.compactSupportFunctional_eq_of_agrees
  intro y _
  simp [φ]

end Langlands
