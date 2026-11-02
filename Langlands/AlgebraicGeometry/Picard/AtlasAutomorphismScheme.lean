import Langlands.AlgebraicGeometry.Picard.RelativeAutomorphisms
import Langlands.CategoryTheory.Sites.PseudofunctorAutomorphismIso
import Langlands.CategoryTheory.OverTotalRepresentable

/-! # Smooth scheme representatives of total Picard automorphisms -/

universe u

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- All automorphisms of pullbacks of the actual family, together with the
map to its base. -/
def atlasAutomorphismPresheaf : AlgebraicSpace.Presheaf S :=
  (automorphismIsoPresheaf (relative f) (Core.mk L)).overTotal ⋙ uliftFunctor.{u + 1}

/-- The full map recording the base of the actual automorphism. -/
def atlasAutomorphismProjection :
    atlasAutomorphismPresheaf f L ⟶ (AlgebraicSpace.schemeYoneda S).obj U where
  app _ := ↾fun x ↦ ULift.up x.down.1
  naturality {_ _} _ := rfl

/-- The actual relative automorphism presheaf is naturally the lifted Iso
presheaf on the same complete slice. -/
def relativeAutomorphismIsoComparison :
    relativeSliceAutomorphismPresheaf f U L ≅
      (U.iteratedSliceBackward.op ⋙
        automorphismIsoPresheaf (relative f) (Core.mk L)) ⋙ uliftFunctor.{u + 1} := by
  letI (T : Over S) : IsGroupoid ((relative f).obj (.mk (op T))) := by
    change IsGroupoid (Core (LineBundle ((relativeSpace f).obj T)))
    infer_instance
  exact isoWhiskerRight (isoWhiskerLeft U.iteratedSliceBackward.op
    (presheafHomAutomorphismIso (relative f) (Core.mk L))) uliftFunctor.{u + 1}

variable {G : Over U.left}
  (e : (AlgebraicSpace.schemeYoneda U.left).obj G ≅
    relativeSliceAutomorphismPresheaf f U L)

/-- A smooth automorphism representative on the slice represents all actual
family automorphisms after totalization. -/
def atlasAutomorphismRepresentation :
    (atlasAutomorphismPresheaf f L).RepresentableBy (U.iteratedSliceBackward.obj G).left := by
  let e₁ := (Functor.RepresentableBy.equivUliftYonedaIso _ G).symm
    (e ≪≫ relativeAutomorphismIsoComparison f L)
  let e₂ := Functor.representableByUliftFunctorEquiv e₁
  let e₃ := Functor.RepresentableBy.ofEquivalence U.iteratedSliceEquiv.symm e₂
  exact Functor.representableByUliftFunctorEquiv.symm e₃.toOverTotal

/-- The full presheaf representation of actual family automorphisms. -/
def atlasAutomorphismSchemeIso :
    (AlgebraicSpace.schemeYoneda S).obj (U.iteratedSliceBackward.obj G).left ≅
      atlasAutomorphismPresheaf f L :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _) (atlasAutomorphismRepresentation f L e)

/-- The represented base projection is precisely the given smooth structure map. -/
lemma atlasAutomorphismSchemeIso_projection :
    (atlasAutomorphismSchemeIso f L e).hom ≫ atlasAutomorphismProjection f L =
      (AlgebraicSpace.schemeYoneda S).map (U.iteratedSliceBackward.obj G).hom := by
  ext T g
  rfl

/-- The smooth-relative-automorphism hypothesis supplies a smooth actual
scheme representing the full total automorphism presheaf. -/
lemma exists_atlasAutomorphismScheme (h : HasSmoothRelativeAutomorphismSchemes f) :
    ∃ (A : Over S) (p : A ⟶ U)
      (e : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasAutomorphismPresheaf f L),
      e.hom ≫ atlasAutomorphismProjection f L = (AlgebraicSpace.schemeYoneda S).map p ∧
        Smooth p.left := by
  obtain ⟨G, ⟨e⟩, hG⟩ := h U L
  exact ⟨_, _, atlasAutomorphismSchemeIso f L e,
    atlasAutomorphismSchemeIso_projection f L e, hG⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
