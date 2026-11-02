import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Actual scheme presentations of a category-valued pseudofunctor -/

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Stacks

variable {S : Scheme.{u}}
  (F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1})
  {U T : Over S}
  (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- The actual point fibre on all schemes over the underlying test scheme. -/
def pointFiberPresheaf : AlgebraicSpace.Presheaf T.left :=
  T.iteratedSliceBackward.op ⋙
    Langlands.CategoryTheory.PseudofunctorPointFiber.presheaf F ξ η

/-- Its points retain an actual map over `S` and an actual isomorphism. -/
abbrev PointFiberPoints (Z : Over T.left) :=
  Langlands.CategoryTheory.PseudofunctorPointFiber.Points F ξ η
    (T.iteratedSliceBackward.obj Z)

/-- Evaluation of the presheaf is the actual point-fibre construction. -/
lemma pointFiberPresheaf_obj (Z : Over T.left) :
    (pointFiberPresheaf F ξ η).obj (op Z) = PointFiberPoints F ξ η Z := rfl

/-- A scheme object gives a smooth surjective presentation when all of its
actual point fibres are represented by smooth surjective schemes over the test. -/
def IsSmoothSurjectivePresentation :
    Prop :=
  ∀ (T : Over S) (η : F.obj (.mk (op T))),
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        pointFiberPresheaf F ξ η) ∧
      Smooth P.hom ∧ Surjective P.hom

/-- Existence of a scheme object with all smooth surjective represented fibres. -/
def HasSmoothSchemeAtlas : Prop :=
  ∃ (U : Over S) (ξ : F.obj (.mk (op U))),
    IsSmoothSurjectivePresentation F ξ

/-- Existence of such a scheme object locally of finite type over the base. -/
def HasLocallyFiniteTypeSmoothSchemeAtlas : Prop :=
  ∃ (U : Over S) (ξ : F.obj (.mk (op U))),
    LocallyOfFiniteType U.hom ∧ IsSmoothSurjectivePresentation F ξ

/-- Forgetting local finite type retains the same actual scheme presentation. -/
lemma HasLocallyFiniteTypeSmoothSchemeAtlas.hasSmoothSchemeAtlas
    (h : HasLocallyFiniteTypeSmoothSchemeAtlas F) :
    HasSmoothSchemeAtlas F := by
  obtain ⟨U, ξ, _, hξ⟩ := h
  exact ⟨U, ξ, hξ⟩

end Langlands.AlgebraicGeometry.Stacks
