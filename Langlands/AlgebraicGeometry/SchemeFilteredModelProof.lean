import Langlands.AlgebraicGeometry.SchemeFilteredModelStatement
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrumProof
import Langlands.AlgebraicGeometry.SchemeLimitModelProof

/-! # Model descent over the original filtered ring stages -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

theorem initialRingModelHomColimitComparison :
    InitialRingModelHomColimitComparison.{u} := by
  intro J _ _ F c hc j₀ X Y
  exact spectrumModelHomColimitComparison (F.obj j₀) (Under j₀)
    (initialRingAlgebraDiagram F j₀) (initialRingAlgebraCocone F j₀ c)
    (initialRingAlgebraCoconeIsColimit F j₀ c hc) X Y

theorem initialRingModelMorphismDescent : InitialRingModelMorphismDescent.{u} := by
  intro J _ _ F c hc j₀ X Y
  dsimp only
  let G := initialRingAlgebraDiagram F j₀
  let d := initialRingAlgebraCocone F j₀ c
  let D := spectrumDiagram (F.obj j₀) G
  let t := spectrumStructure (F.obj j₀) G
  let C := spectrumCone (F.obj j₀) G d
  let p := spectrumBaseMap (F.obj j₀) G d
  let hp := spectrumCone_compat (F.obj j₀) G d
  obtain ⟨hs, hi, he⟩ := modelMorphismDescent (Under j₀)ᵒᵖ D
    (Spec (F.obj j₀)) X.left Y.left t X.hom Y.hom C
    (spectrumConeIsLimit (F.obj j₀) G d (initialRingAlgebraCoconeIsColimit F j₀ c hc))
    p hp
  refine ⟨?_, ?_, ?_⟩
  · intro hqc hqs hfp f
    obtain ⟨j, fj, hj⟩ := hs hqc hqs hfp f
    exact ⟨j.unop, fj, hj⟩
  · intro hqc hft i j fi fj h
    obtain ⟨k, r, s, hrs⟩ := hi hqc hft (op i) (op j) fi fj h
    exact ⟨k.unop, r.unop, s.unop, hrs⟩
  · intro hqcx hqsx hfpx hqcy hqsy hfpy e he'
    obtain ⟨j, ej, hej, hj⟩ := he hqcx hqsx hfpx hqcy hqsy hfpy e he'
    exact ⟨j.unop, ej, hej, hj⟩

/-- Both actual-ring model-descent assertions retain the original maps. -/
theorem initialRingModelDescent : InitialRingModelDescent.{u} :=
  ⟨initialRingModelHomColimitComparison, initialRingModelMorphismDescent⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
