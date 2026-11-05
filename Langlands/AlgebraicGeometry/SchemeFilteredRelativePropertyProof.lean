import Langlands.AlgebraicGeometry.SchemeFilteredRelativePropertyStatement
import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyProof
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Proof of original-ring relative smoothness and flatness descent -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

private theorem spectrumRelativePropertyDescent
    (P : MorphismProperty Scheme.{u}) (hdesc : RelativePropertyDescent P) :
    SpectrumRelativePropertyDescent P := by
  intro R _ J _ _ F c hc X Y f _ _ _ _
  refine (hdesc (spectrumDiagram R F) (spectrumStructure R F)
      X.hom Y.hom f.left (Over.w f) (spectrumCone R F c)
      (spectrumConeIsLimit R F c hc) (spectrumBaseMap R F c)
      (spectrumCone_compat R F c)).trans ?_
  exact ⟨fun ⟨j, h⟩ ↦ ⟨j.unop, h⟩, fun ⟨j, h⟩ ↦ ⟨op j, h⟩⟩

private theorem initialRingRelativePropertyDescent
    (P : MorphismProperty Scheme.{u}) (hdesc : SpectrumRelativePropertyDescent P) :
    InitialRingRelativePropertyDescent P := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _
  exact hdesc (F.obj j₀) (initialRingAlgebraDiagram F j₀)
    (initialRingAlgebraCocone F j₀ c) (initialRingAlgebraCoconeIsColimit F j₀ c hc)
      X Y f

private theorem finitePresentationInitialRingRelativePropertyDescent
    (P : MorphismProperty Scheme.{u}) (hdesc : InitialRingRelativePropertyDescent P) :
    FinitePresentationInitialRingRelativePropertyDescent P := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _ _ _
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFinitePresentation f.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp f.left Y.hom
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : QuasiSeparated f.left := QuasiSeparated.of_comp f.left Y.hom
  exact hdesc F c hc j₀ X Y f

theorem spectrumRelativeSmoothFlatDescent : SpectrumRelativeSmoothFlatDescent.{u} :=
  ⟨spectrumRelativePropertyDescent @Smooth relativeSmoothDescent,
    spectrumRelativePropertyDescent @Flat relativeFlatDescent⟩

theorem initialRingRelativeSmoothFlatDescent : InitialRingRelativeSmoothFlatDescent.{u} :=
  ⟨initialRingRelativePropertyDescent @Smooth spectrumRelativeSmoothFlatDescent.1,
    initialRingRelativePropertyDescent @Flat spectrumRelativeSmoothFlatDescent.2⟩

theorem finitePresentationInitialRingRelativeSmoothFlatDescent :
    FinitePresentationInitialRingRelativeSmoothFlatDescent.{u} :=
  ⟨finitePresentationInitialRingRelativePropertyDescent @Smooth
      initialRingRelativeSmoothFlatDescent.1,
    finitePresentationInitialRingRelativePropertyDescent @Flat
      initialRingRelativeSmoothFlatDescent.2⟩

/-- Both properties in all three forms use the actual original ring maps. -/
theorem ringSystemRelativeSmoothFlatDescent : RingSystemRelativeSmoothFlatDescent.{u} :=
  ⟨spectrumRelativeSmoothFlatDescent, initialRingRelativeSmoothFlatDescent,
    finitePresentationInitialRingRelativeSmoothFlatDescent⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
