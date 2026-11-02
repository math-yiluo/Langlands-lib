import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Langlands.AlgebraicGeometry.Stacks.SchemeAtlas
import Langlands.CategoryTheory.Sites.PseudofunctorHomLift
import Mathlib.CategoryTheory.Whiskering

/-! # Generic and concrete atlases of the actual Picard pseudofunctor -/

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The same actual line bundles with explicitly lifted isomorphism morphisms. -/
abbrev relativeHomLift : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1} :=
  Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{u + 1} (relative f)

variable {U T : Over S}
  (L : LineBundle ((relativeSpace f).obj U))
  (M : LineBundle ((relativeSpace f).obj T))

/-- The generic and concrete point-fibre presheaves agree naturally on all tests. -/
def pointFiberPresheafHomLiftIso :
    Stacks.pointFiberPresheaf (relativeHomLift f)
      (ULiftHom.objUp.{u + 1, u + 1} (Core.mk L))
      (ULiftHom.objUp.{u + 1, u + 1} (Core.mk M)) ≅
        pointFiberPresheaf f L M :=
  Functor.isoWhiskerLeft T.iteratedSliceBackward.op
      (Langlands.CategoryTheory.PseudofunctorHomLift.presheafIso.{u + 1}
        (F := relative f) (Core.mk L) (Core.mk M)) ≪≫
    (Functor.associator _ _ _).symm

/-- A generic presentation of the lifted actual pseudofunctor is exactly the
concrete Picard presentation, with the same family and representing schemes. -/
lemma isSmoothSurjectivePresentation_homLift_iff :
    Stacks.IsSmoothSurjectivePresentation (relativeHomLift f)
      (ULiftHom.objUp.{u + 1, u + 1} (Core.mk L)) ↔
        IsSmoothSurjectivePresentation f L := by
  constructor
  · intro h T M
    obtain ⟨P, ⟨e⟩, hsm, hsur⟩ := h T (ULiftHom.objUp.{u + 1, u + 1} (Core.mk M))
    exact ⟨P, ⟨e ≪≫ pointFiberPresheafHomLiftIso f L M⟩, hsm, hsur⟩
  · intro h T η
    obtain ⟨P, ⟨e⟩, hsm, hsur⟩ := h T (ULiftHom.objDown.{u + 1, u + 1} η).of
    exact ⟨P, ⟨e ≪≫ (pointFiberPresheafHomLiftIso f L (ULiftHom.objDown.{u + 1, u + 1} η).of).symm⟩, hsm, hsur⟩

/-- Forgetting the explicit universe lift changes no scheme-atlas condition. -/
lemma hasSmoothSchemeAtlas_homLift_iff :
    Stacks.HasSmoothSchemeAtlas (relativeHomLift f) ↔ HasSmoothSchemeAtlas f := by
  constructor
  · rintro ⟨U, ξ, hξ⟩
    exact ⟨U, (ULiftHom.objDown.{u + 1, u + 1} ξ).of,
      (isSmoothSurjectivePresentation_homLift_iff f (ULiftHom.objDown.{u + 1, u + 1} ξ).of).mp hξ⟩
  · rintro ⟨U, L, hL⟩
    exact ⟨U, ULiftHom.objUp.{u + 1, u + 1} (Core.mk L),
      (isSmoothSurjectivePresentation_homLift_iff f L).mpr hL⟩

/-- Local finite type is retained for the same actual atlas scheme over the base. -/
lemma hasLocallyFiniteTypeSmoothSchemeAtlas_homLift_iff :
    Stacks.HasLocallyFiniteTypeSmoothSchemeAtlas (relativeHomLift f) ↔
      HasLocallyFiniteTypeSmoothSchemeAtlas f := by
  constructor
  · rintro ⟨U, ξ, hU, hξ⟩
    exact ⟨U, (ULiftHom.objDown.{u + 1, u + 1} ξ).of, hU,
      (isSmoothSurjectivePresentation_homLift_iff f (ULiftHom.objDown.{u + 1, u + 1} ξ).of).mp hξ⟩
  · rintro ⟨U, L, hU, hL⟩
    exact ⟨U, ULiftHom.objUp.{u + 1, u + 1} (Core.mk L), hU,
      (isSmoothSurjectivePresentation_homLift_iff f L).mpr hL⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
