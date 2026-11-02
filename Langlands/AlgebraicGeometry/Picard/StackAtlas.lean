import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Actual scheme presentations of the relative Picard groupoid -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {U T : Over S}
  (L : LineBundle ((relativeSpace f).obj U))
  (M : LineBundle ((relativeSpace f).obj T))

/-- The actual point fibre, lifted to the algebraic-space value universe. -/
def pointFiberPresheaf : AlgebraicSpace.Presheaf T.left :=
  (T.iteratedSliceBackward.op ⋙
    Langlands.CategoryTheory.PseudofunctorPointFiber.presheaf
      (relative f) (Core.mk L) (Core.mk M)) ⋙ uliftFunctor.{u + 1}

/-- A fibre point retains both the map to the atlas and the bundle isomorphism. -/
abbrev PointFiberPoints (Z : Over T.left) : Type u :=
  Langlands.CategoryTheory.PseudofunctorPointFiber.Points
    (relative f) (Core.mk L) (Core.mk M) (T.iteratedSliceBackward.obj Z)

/-- Evaluation lifts the actual fibre-point type, without quotienting it. -/
lemma pointFiberPresheaf_obj (Z : Over T.left) :
    (pointFiberPresheaf f L M).obj (op Z) =
      ULift.{u + 1} (PointFiberPoints f L M Z) := rfl

/-- A family of line bundles gives a smooth surjective presentation if every
actual point fibre is represented by a smooth surjective scheme over the test. -/
def IsSmoothSurjectivePresentation : Prop :=
  ∀ (T : Over S) (M : LineBundle ((relativeSpace f).obj T)),
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        pointFiberPresheaf f L M) ∧
      Smooth P.hom ∧ Surjective P.hom

/-- An actual scheme and line bundle give a smooth scheme atlas. -/
def HasSmoothSchemeAtlas : Prop :=
  ∃ (U : Over S) (L : LineBundle ((relativeSpace f).obj U)),
    IsSmoothSurjectivePresentation f L

/-- Such an atlas whose scheme is locally of finite type over the base. -/
def HasLocallyFiniteTypeSmoothSchemeAtlas : Prop :=
  ∃ (U : Over S) (L : LineBundle ((relativeSpace f).obj U)),
    LocallyOfFiniteType U.hom ∧ IsSmoothSurjectivePresentation f L

/-- Forgetting local finite type retains the same family and actual fibres. -/
lemma HasLocallyFiniteTypeSmoothSchemeAtlas.hasSmoothSchemeAtlas
    (h : HasLocallyFiniteTypeSmoothSchemeAtlas f) :
    HasSmoothSchemeAtlas f := by
  obtain ⟨U, L, _, hL⟩ := h
  exact ⟨U, L, hL⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
