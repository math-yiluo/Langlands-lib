import Langlands.AlgebraicGeometry.Picard.AtlasArrowPresheaf
import Langlands.CategoryTheory.OverTotalRepresentable

/-! # A scheme representing the full arrows of a Picard atlas -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))
  {P : Over U.left}
  (e : (AlgebraicSpace.schemeYoneda U.left).obj P ≅ pointFiberPresheaf f L L)

/-- The actual point-fibre representative gives a representation of all arrows. -/
def atlasArrowRepresentation :
    (atlasArrowPresheaf f L).RepresentableBy (U.iteratedSliceBackward.obj P).left := by
  let e₁ := (Functor.RepresentableBy.equivUliftYonedaIso _ P).symm e
  let e₂ := Functor.representableByUliftFunctorEquiv e₁
  let e₃ := Functor.RepresentableBy.ofEquivalence U.iteratedSliceEquiv.symm e₂
  exact Functor.representableByUliftFunctorEquiv.symm e₃.toOverTotal

/-- The representation is an isomorphism of the full presheaves on schemes over S. -/
def atlasArrowSchemeIso :
    (AlgebraicSpace.schemeYoneda S).obj (U.iteratedSliceBackward.obj P).left ≅
      atlasArrowPresheaf f L :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _) (atlasArrowRepresentation f L e)

/-- The second endpoint is the original smooth point-fibre projection. -/
lemma atlasArrowSchemeIso_snd :
    (atlasArrowSchemeIso f L e).hom ≫ atlasArrowSnd f L =
      (AlgebraicSpace.schemeYoneda S).map (U.iteratedSliceBackward.obj P).hom := by
  ext T g
  rfl

/-- A smooth surjective actual atlas represents the full arrow presheaf by a
scheme whose second endpoint is smooth and surjective. -/
lemma exists_atlasArrowScheme_snd (hL : IsSmoothSurjectivePresentation f L) :
    ∃ (A : Over S) (t : A ⟶ U)
      (e : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L),
      e.hom ≫ atlasArrowSnd f L = (AlgebraicSpace.schemeYoneda S).map t ∧
        Smooth t.left ∧ Surjective t.left := by
  obtain ⟨P, ⟨e⟩, hP, hsP⟩ := hL U L
  exact ⟨_, _, atlasArrowSchemeIso f L e, atlasArrowSchemeIso_snd f L e, hP, hsP⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
