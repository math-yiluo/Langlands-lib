import Langlands.AlgebraicGeometry.SchemeFilteredOpenImmersionStatement
import Langlands.AlgebraicGeometry.SchemeLimitOpenImmersionProof

/-! # Proof of open-immersion descent over the original ring system -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

theorem spectrumOpenImmersionDescent : SpectrumOpenImmersionDescent.{u} := by
  intro R _ J _ _ F c hc X Y f _ _ _ _
  constructor
  · intro H
    let := H
    obtain ⟨j, h⟩ := exists_isOpenImmersion_baseChangeMap
      (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom f.left (Over.w f)
      (spectrumCone R F c) (spectrumConeIsLimit R F c hc) (spectrumBaseMap R F c)
      (spectrumCone_compat R F c)
    exact ⟨j.unop, h⟩
  · rintro ⟨j, H⟩
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (cone_baseChangeMap_isPullback X.hom Y.hom f.left (Over.w f)
        (spectrumDiagram R F) (spectrumStructure R F) (spectrumCone R F c)
        (spectrumBaseMap R F c) (spectrumCone_compat R F c) (op j)).flip H

theorem initialRingOpenImmersionDescent : InitialRingOpenImmersionDescent.{u} := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _
  exact spectrumOpenImmersionDescent (F.obj j₀) (initialRingAlgebraDiagram F j₀)
    (initialRingAlgebraCocone F j₀ c) (initialRingAlgebraCoconeIsColimit F j₀ c hc)
      X Y f

theorem finitePresentationInitialRingOpenImmersionDescent :
    FinitePresentationInitialRingOpenImmersionDescent.{u} := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _ _ _
  exact initialRingOpenImmersionDescent F c hc j₀ X Y f

/-- All three forms use the original maps and retain arbitrary models. -/
theorem ringSystemOpenImmersionDescent : RingSystemOpenImmersionDescent.{u} :=
  ⟨spectrumOpenImmersionDescent, initialRingOpenImmersionDescent,
    finitePresentationInitialRingOpenImmersionDescent⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
