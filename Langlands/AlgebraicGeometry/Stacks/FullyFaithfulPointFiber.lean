import Langlands.AlgebraicGeometry.Stacks.SchemeAtlas
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberTransport
import Mathlib.CategoryTheory.Whiskering

/-! # Scheme-represented point fibres under fully faithful transformations -/

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Stacks

variable {S : Scheme.{u}}
  {F G : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1}}
  (α : Pseudofunctor.StrongTrans F G)
  (hα : ∀ Z : Over S,
    (Langlands.CategoryTheory.PseudofunctorPointFiberTransport.component α Z).FullyFaithful)
  {U T : Over S} (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

include hα

/-- Full-slice scheme point fibres agree for the actual image objects. -/
def fullyFaithfulPointFiberIso :
    pointFiberPresheaf F ξ η ≅
      pointFiberPresheaf G ((α.app (.mk (op U))).toFunctor.obj ξ)
        ((α.app (.mk (op T))).toFunctor.obj η) :=
  Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (Langlands.CategoryTheory.PseudofunctorPointFiberTransport.presheafIso α ξ η hα)

/-- Natural scheme representations and their smooth surjective projections
transfer in both directions, keeping the same represented scheme. -/
lemma fullyFaithfulPointFiber_smoothSurjectiveRepresented_iff :
    (∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf F ξ η) ∧
        Smooth P.hom ∧ Surjective P.hom) ↔
    (∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        pointFiberPresheaf G ((α.app (.mk (op U))).toFunctor.obj ξ)
          ((α.app (.mk (op T))).toFunctor.obj η)) ∧
        Smooth P.hom ∧ Surjective P.hom) := by
  constructor
  · rintro ⟨P, ⟨e⟩, hsm, hsur⟩
    exact ⟨P, ⟨e ≪≫ fullyFaithfulPointFiberIso α hα ξ η⟩, hsm, hsur⟩
  · rintro ⟨P, ⟨e⟩, hsm, hsur⟩
    exact ⟨P, ⟨e ≪≫ (fullyFaithfulPointFiberIso α hα ξ η).symm⟩, hsm, hsur⟩

/-- A presentation condition on `F` is exactly the ambient point-fibre
representation condition for all of its actual image objects. -/
lemma isSmoothSurjectivePresentation_iff_on_fullyFaithful_image :
    IsSmoothSurjectivePresentation F ξ ↔
      ∀ (T : Over S) (η : F.obj (.mk (op T))),
        ∃ P : Over T.left,
          Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
            pointFiberPresheaf G ((α.app (.mk (op U))).toFunctor.obj ξ)
              ((α.app (.mk (op T))).toFunctor.obj η)) ∧
            Smooth P.hom ∧ Surjective P.hom := by
  constructor
  · intro h T η
    exact (fullyFaithfulPointFiber_smoothSurjectiveRepresented_iff α hα ξ η).mp (h T η)
  · intro h T η
    exact (fullyFaithfulPointFiber_smoothSurjectiveRepresented_iff α hα ξ η).mpr (h T η)

/-- An ambient presentation whose atlas object is in the actual image
restricts to a presentation of the source pseudofunctor. -/
lemma isSmoothSurjectivePresentation_of_fullyFaithful_image
    (h : IsSmoothSurjectivePresentation G ((α.app (.mk (op U))).toFunctor.obj ξ)) :
    IsSmoothSurjectivePresentation F ξ := by
  intro T η
  exact (fullyFaithfulPointFiber_smoothSurjectiveRepresented_iff α hα ξ η).mpr
    (h T ((α.app (.mk (op T))).toFunctor.obj η))

end Langlands.AlgebraicGeometry.Stacks
