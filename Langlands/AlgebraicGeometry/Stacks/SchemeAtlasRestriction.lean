import Langlands.AlgebraicGeometry.Stacks.FullyFaithfulPointFiber
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberAtlasRestriction
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberObjectIso

/-! # Restricting actual smooth scheme atlases along fully faithful inclusions -/

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Stacks

open Langlands.CategoryTheory.PseudofunctorPointFiberTransport

variable {S : Scheme.{u}}
  {F G : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1}}
  (α : Pseudofunctor.StrongTrans F G)
  (hα : ∀ Z : Over S, (component α Z).FullyFaithful)
  {U V : Over S} (i : V ⟶ U) [Mono i]
  (ξ : G.obj (.mk (op U))) (L : F.obj (.mk (op V)))
  (e : (component α V).obj L ≅ (G.map i.op.toLoc).toFunctor.obj ξ)

variable {T : Over S} (η : F.obj (.mk (op T)))
  (hlift : ∀ (Z : Over T)
    (x : Langlands.CategoryTheory.PseudofunctorPointFiber.Points G ξ
      ((component α T).obj η) Z), ∃ a : Z.left ⟶ V, a ≫ i = x.1)

/-- The restricted source atlas has the same entire scheme point fibre as the
ambient atlas against the image test object. -/
def restrictedAtlasPointFiberIso :
    pointFiberPresheaf F L η ≅ pointFiberPresheaf G ξ ((component α T).obj η) :=
  fullyFaithfulPointFiberIso α hα L η ≪≫
    Functor.isoWhiskerLeft T.iteratedSliceBackward.op
      (Langlands.CategoryTheory.PseudofunctorPointFiberObjectIso.presheafIso G e
        ((component α T).obj η) ≪≫
      Langlands.CategoryTheory.PseudofunctorPointFiberAtlasRestriction.presheafIso G i ξ
        ((component α T).obj η) hlift)

include hα i e hlift

/-- Restriction retains the very same representing scheme and smooth surjective
map for every test object. -/
lemma restrictedAtlasPointFiber_smoothSurjectiveRepresented
    (h : ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        pointFiberPresheaf G ξ ((component α T).obj η)) ∧
      Smooth P.hom ∧ Surjective P.hom) :
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf F L η) ∧
      Smooth P.hom ∧ Surjective P.hom := by
  obtain ⟨P, ⟨p⟩, hsm, hsur⟩ := h
  exact ⟨P, ⟨p ≪≫ (restrictedAtlasPointFiberIso α hα i ξ L e η hlift).symm⟩,
    hsm, hsur⟩

omit hlift

variable (hall : ∀ (T : Over S) (η : F.obj (.mk (op T))) (Z : Over T)
  (x : Langlands.CategoryTheory.PseudofunctorPointFiber.Points G ξ
    ((component α T).obj η) Z), ∃ a : Z.left ⟶ V, a ≫ i = x.1)

include hall

/-- An ambient smooth surjective presentation restricts when all its points
against image test objects factor through the monomorphic atlas restriction. -/
lemma isSmoothSurjectivePresentation_of_restrictedAtlas
    (hξ : IsSmoothSurjectivePresentation G ξ) :
    IsSmoothSurjectivePresentation F L := by
  intro T η
  exact restrictedAtlasPointFiber_smoothSurjectiveRepresented α hα i ξ L e η
    (hall T η) (hξ T ((component α T).obj η))

/-- A locally finite type restricted atlas scheme gives the corresponding
locally finite type smooth scheme atlas of the source pseudofunctor. -/
lemma hasLocallyFiniteTypeSmoothSchemeAtlas_of_restrictedAtlas
    (hV : LocallyOfFiniteType V.hom) (hξ : IsSmoothSurjectivePresentation G ξ) :
    HasLocallyFiniteTypeSmoothSchemeAtlas F :=
  ⟨V, L, hV, isSmoothSurjectivePresentation_of_restrictedAtlas α hα i ξ L e hall hξ⟩

end Langlands.AlgebraicGeometry.Stacks
