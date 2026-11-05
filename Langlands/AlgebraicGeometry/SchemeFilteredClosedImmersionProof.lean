import Langlands.AlgebraicGeometry.SchemeFilteredClosedImmersionStatement
import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionProof

/-! # Proof of closed-immersion descent over the original ring system -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

theorem spectrumClosedImmersionDescent : SpectrumClosedImmersionDescent.{u} := by
  intro R _ J _ _ F c hc X Y f _ _ _ _
  refine (relativeClosedImmersionDescent (spectrumDiagram R F) (spectrumStructure R F)
      X.hom Y.hom f.left (Over.w f) (spectrumCone R F c)
      (spectrumConeIsLimit R F c hc) (spectrumBaseMap R F c)
      (spectrumCone_compat R F c)).trans ?_
  exact ⟨fun ⟨j, h⟩ ↦ ⟨j.unop, h⟩, fun ⟨j, h⟩ ↦ ⟨op j, h⟩⟩

theorem initialRingClosedImmersionDescent : InitialRingClosedImmersionDescent.{u} := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _
  exact spectrumClosedImmersionDescent (F.obj j₀) (initialRingAlgebraDiagram F j₀)
    (initialRingAlgebraCocone F j₀ c) (initialRingAlgebraCoconeIsColimit F j₀ c hc)
      X Y f

theorem finitePresentationInitialRingClosedImmersionDescent :
    FinitePresentationInitialRingClosedImmersionDescent.{u} := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _ _ _
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : QuasiSeparated f.left := QuasiSeparated.of_comp f.left Y.hom
  exact initialRingClosedImmersionDescent F c hc j₀ X Y f

/-- All three forms use the original maps and retain arbitrary models. -/
theorem ringSystemClosedImmersionDescent : RingSystemClosedImmersionDescent.{u} :=
  ⟨spectrumClosedImmersionDescent, initialRingClosedImmersionDescent,
    finitePresentationInitialRingClosedImmersionDescent⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
