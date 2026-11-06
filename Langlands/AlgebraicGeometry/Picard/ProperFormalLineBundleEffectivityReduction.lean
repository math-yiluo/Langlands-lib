import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceStatement
import Langlands.AlgebraicGeometry.Picard.ProperFormalLineBundleEffectivityStatement
import Langlands.AlgebraicGeometry.Picard.AdicPullbackRankOnePromotion
import Langlands.AlgebraicGeometry.Picard.LineBundleFinitePresentation

/-! # Proper formal line-bundle effectivity from coherent formal existence -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Coherent formal existence for proper schemes over complete local noetherian
rings implies effectivity of compatible systems of actual formal line bundles. -/
theorem properFormalLineBundleEffectivity_of_coherentExistence
    (h : Modules.ProperFormalCoherentExistenceStatement.{u}) :
    ProperFormalLineBundleEffectivityStatement.{u} := by
  intro R _ _ _ _ X f hf F
  obtain ⟨M, hM, hAlg⟩ := h R X f hf F.toModuleSystem
    (fun n ↦ (F.obj n).property.isFinitePresentation)
  have hPullback : ∀ n : ℕ, IsLocallyFreeRankOne
      ((Scheme.Modules.pullback
        (FormalLineBundle.adicProjection f (IsLocalRing.maximalIdeal R) n)).obj M) := by
    obtain ⟨e⟩ := hAlg
    exact fun n ↦ (F.obj n).property.of_iso (e.component n).symm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let L := lineBundleOfAdicPullbacks f M hPullback
  exact ⟨L, FormalLineBundleSystem.isAlgebraization_of_module L.property hAlg⟩

end Langlands.AlgebraicGeometry.Picard
