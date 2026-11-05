import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrumStatement
import Langlands.AlgebraicGeometry.SchemeLimitModelColimitProof

/-! # Actual relative Hom comparison over filtered algebra colimits -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- The actual spectrum construction and quotient equivalence specialize the
scheme-model comparison to the original filtered algebra index. -/
theorem spectrumModelHomColimitComparison : SpectrumModelHomColimitComparison.{u} := by
  intro R _ J _ _ F c hc X Y
  obtain ⟨hinj, hsurj, _⟩ := modelHomColimitComparison Jᵒᵖ (spectrumDiagram R F)
    (Spec (CommRingCat.of R)) X.left Y.left (spectrumStructure R F) X.hom Y.hom
    (spectrumCone R F c) (spectrumConeIsLimit R F c hc)
    (spectrumBaseMap R F c) (spectrumCone_compat R F c)
  have hmap : spectrumHomColimitMap R F c X Y =
      homColimitMap (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom
        (spectrumCone R F c) (spectrumBaseMap R F c) (spectrumCone_compat R F c) ∘
          spectrumHomColimitEquiv R F X Y := by
    funext z
    exact spectrumHomColimitMap_eq R F c X Y z
  have hi : QuasiCompact X.hom → LocallyOfFiniteType Y.hom →
      Function.Injective (spectrumHomColimitMap R F c X Y) := by
    intro hqc hft
    rw [hmap]
    exact (hinj hqc hft).comp (spectrumHomColimitEquiv R F X Y).injective
  have hs : QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFinitePresentation Y.hom →
      Function.Surjective (spectrumHomColimitMap R F c X Y) := by
    intro hqc hqs hfp
    rw [hmap]
    exact (hsurj hqc hqs hfp).comp (spectrumHomColimitEquiv R F X Y).surjective
  refine ⟨hi, hs, ?_⟩
  intro hqc hqs hfp
  let := hfp
  have hbij : Function.Bijective (spectrumHomColimitMap R F c X Y) :=
    ⟨hi hqc inferInstance, hs hqc hqs hfp⟩
  exact ⟨hbij, (spectrumHomCoconeTypes R F c X Y).isColimit_iff.mp ⟨hbij⟩⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
