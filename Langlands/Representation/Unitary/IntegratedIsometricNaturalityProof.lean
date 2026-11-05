import Langlands.Representation.Unitary.IntegratedIsometricNaturalityStatement
import Mathlib.Analysis.Normed.Module.Completion

noncomputable section

namespace Langlands.Analysis

open MeasureTheory

universe uG uE

/-- Naturality follows from actual Bochner integration inside a closed subspace. -/
theorem integratedIsometricNaturality : IntegratedIsometricNaturalityStatement.{uG, uE} := by
  intro G _ _ E _ _ _ μ π hπnorm hπmeas f hf
  dsimp only
  intro P hPc hPi
  let : CompleteSpace P := hPc.completeSpace_coe
  let Φ (x : P) (g : G) : P :=
    ⟨f g • π g x, P.smul_mem (f g) (hPi g x x.property)⟩
  have hI (x : P) :
      (∫ g, f g • π g x ∂μ) = ((∫ g, Φ x g ∂μ : P) : E) := by
    exact P.subtypeₗᵢ.integral_comp_comm (Φ x)
  have hTP : ∀ (x : E), x ∈ P →
      integratedIsometricAction μ π hπnorm hπmeas f hf x ∈ P := by
    intro x hx
    change (∫ g, f g • π g x ∂μ) ∈ P
    rw [hI ⟨x, hx⟩]
    exact (∫ g, Φ ⟨x, hx⟩ g ∂μ : P).property
  refine ⟨hTP, ?_⟩
  intro Q U hU x
  let L : P →ₗᵢ[ℂ] E := Q.subtypeₗᵢ.comp U.toLinearIsometry
  have hΦ (g : G) : L (Φ x g) = f g • π g (U x : E) := by
    change (U ((f g) • (⟨π g x, hPi g x x.property⟩ : P)) : E) = _
    rw [map_smul]
    exact congrArg (fun y : E => f g • y) (hU g x)
  have hx : (⟨integratedIsometricAction μ π hπnorm hπmeas f hf x,
      hTP x x.property⟩ : P) = ∫ g, Φ x g ∂μ := by
    apply Subtype.ext
    exact hI x
  change (U (⟨integratedIsometricAction μ π hπnorm hπmeas f hf x,
      hTP x x.property⟩ : P) : E) = _
  rw [hx]
  calc
    (U (∫ g, Φ x g ∂μ) : E) = ∫ g, L (Φ x g) ∂μ :=
      (L.integral_comp_comm (Φ x)).symm
    _ = ∫ g, f g • π g (U x : E) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hΦ)
    _ = integratedIsometricAction μ π hπnorm hπmeas f hf (U x : E) := rfl

end Langlands.Analysis
