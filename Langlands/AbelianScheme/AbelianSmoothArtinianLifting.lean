import Langlands.AbelianScheme.AbelianSmoothArtinianLiftingStatement
import Langlands.AbelianScheme.ArtinianSquareVanishing

/-! # Smooth proper pointed lifts of abelian schemes across elementary Artinian extensions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Langlands.AbelianScheme

open ArtinianConstantCharts

/-- The underlying pointed scheme of an abelian scheme over the thinner ring of an elementary
extension of characteristic-zero local Artinian rings is the reduction of a smooth proper
pointed scheme over the thicker ring. -/
theorem abelianSmoothArtinianLifting : AbelianSmoothArtinianLiftingStatement.{u} := by
  intro R' R _ _ _ _ _ _ _ φ hφ hker B
  obtain ⟨S, rfl⟩ := Setting.exists φ hφ (le_maximalIdeal (RingHom.ker_ne_top φ))
  have : Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥) := ⟨hker⟩
  obtain ⟨K⟩ := Setting.Charts.exists S B
  obtain ⟨L⟩ := K.nonempty_liftedTransitions_of_elementary
  exact L.exists_smoothLift

end Langlands.AbelianScheme
