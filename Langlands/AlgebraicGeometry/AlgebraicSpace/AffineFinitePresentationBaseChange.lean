import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFinitePresentationRepresentable
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeBaseChange

/-! # Base change of affine finitely presented presheaf representations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

variable {B T : Scheme.{u}} {F : Presheaf B}

/-- Restrict an actual affine finitely presented representation, retaining
its full natural comparison and both properties of its base-changed map. -/
def affineRepresentationBaseChange (g : T ⟶ B) (I : Over B)
    (e : (schemeYoneda B).obj I ≅ F)
    [IsAffineHom I.hom] [LocallyOfFinitePresentation I.hom] :
    { _e : (schemeYoneda T).obj ((Over.pullback g).obj I) ≅ (Over.map g).op ⋙ F //
      IsAffineHom ((Over.pullback g).obj I).hom ∧
        LocallyOfFinitePresentation ((Over.pullback g).obj I).hom } := by
  refine ⟨representedBaseChangeIso g I e, ?_, ?_⟩
  · change IsAffineHom (pullback.snd I.hom g)
    exact MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom I.hom)
  · change LocallyOfFinitePresentation (pullback.snd I.hom g)
    infer_instance

/-- Affine finite-presentation representability is preserved by restriction
along an arbitrary morphism of base schemes. -/
lemma IsAffineFinitePresentationRepresentable.baseChange
    (hF : IsAffineFinitePresentationRepresentable F) (g : T ⟶ B) :
    IsAffineFinitePresentationRepresentable ((Over.map g).op ⋙ F) := by
  obtain ⟨I, ⟨e⟩, hAffine, hFP⟩ := hF
  let d := affineRepresentationBaseChange g I e
  exact ⟨(Over.pullback g).obj I, ⟨d.val⟩, d.property⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
