import Langlands.AlgebraicGeometry.SchemeFilteredAffinenessStatement
import Langlands.AlgebraicGeometry.SchemeLimitAffineProof

/-! # Proof of affineness descent over the original ring system -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

theorem spectrumAffinenessDescent : SpectrumAffinenessDescent.{u} := by
  intro R _ J _ _ F c hc X Y f _ _ _
  refine (relativeAffinenessDescent (spectrumDiagram R F) (spectrumStructure R F)
      X.hom Y.hom f.left (Over.w f) (spectrumCone R F c)
      (spectrumConeIsLimit R F c hc) (spectrumBaseMap R F c)
      (spectrumCone_compat R F c)).trans ?_
  exact ⟨fun ⟨j, h⟩ ↦ ⟨j.unop, h⟩, fun ⟨j, h⟩ ↦ ⟨op j, h⟩⟩

theorem initialRingAffinenessDescent : InitialRingAffinenessDescent.{u} := by
  intro J _ _ F c hc j₀ X Y f _ _ _
  exact spectrumAffinenessDescent (F.obj j₀) (initialRingAlgebraDiagram F j₀)
    (initialRingAlgebraCocone F j₀ c) (initialRingAlgebraCoconeIsColimit F j₀ c hc)
      X Y f

theorem finitePresentationInitialRingAffinenessDescent :
    FinitePresentationInitialRingAffinenessDescent.{u} := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _ _ _
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : QuasiSeparated f.left := QuasiSeparated.of_comp f.left Y.hom
  exact initialRingAffinenessDescent F c hc j₀ X Y f

/-- All three forms use the original maps and retain arbitrary models. -/
theorem ringSystemAffinenessDescent : RingSystemAffinenessDescent.{u} :=
  ⟨spectrumAffinenessDescent, initialRingAffinenessDescent,
    finitePresentationInitialRingAffinenessDescent⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
