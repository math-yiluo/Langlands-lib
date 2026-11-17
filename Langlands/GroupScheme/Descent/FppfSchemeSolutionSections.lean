import Langlands.GroupScheme.Descent.SchemeSolutionSections
import Langlands.GroupScheme.Descent.FppfSchemeSolution

/-! # Sections of scheme solutions along fppf covers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent

variable {B S Z : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  {D : Datum p G}

namespace SchemeSolution

variable (s : SchemeSolution D)

variable [Flat p] [LocallyOfFinitePresentation p] [Surjective p]

theorem fppfLocalSection_injective (U : Over B) :
    Function.Injective (s.localSection (U := U)) := by
  intro f g h
  apply (Over.pullback p).map_injective
  exact (cancel_mono s.iso.hom).mp h

omit [Flat p] [LocallyOfFinitePresentation p] [Surjective p] in
private theorem fppfInvariant_section {U : Over B}
    (x : sectionSubgroup (D := D) U) (a b : Z ⟶ ((Over.pullback p).obj U).left)
    (hab : a ≫ pullback.fst U.hom p = b ≫ pullback.fst U.hom p) :
    a ≫ x.val.left ≫ s.proj = b ≫ x.val.left ≫ s.proj := by
  have h := (s.sectionTransport_eq_iff _ _ _ _ _).mp (x.property Z a b hab)
  change (a ≫ x.val.left) ≫ s.proj = (b ≫ x.val.left) ≫ s.proj at h
  simpa only [Category.assoc] using h

private def fppfSectionDescLeft {U : Over B} (x : sectionSubgroup (D := D) U) :
    U.left ⟶ s.obj.left :=
  EffectiveEpi.desc (pullback.fst U.hom p) (x.val.left ≫ s.proj)
    (fun a b hab => s.fppfInvariant_section x a b hab)

@[reassoc] private theorem fppfSectionDescLeft_fac {U : Over B} (x : sectionSubgroup (D := D) U) :
    pullback.fst U.hom p ≫ s.fppfSectionDescLeft x = x.val.left ≫ s.proj :=
  EffectiveEpi.fac _ _ _

private theorem fppfSectionDescLeft_over {U : Over B} (x : sectionSubgroup (D := D) U) :
    s.fppfSectionDescLeft x ≫ s.obj.hom = U.hom := by
  apply (cancel_epi (pullback.fst U.hom p)).mp
  rw [← Category.assoc, s.fppfSectionDescLeft_fac]
  rw [Category.assoc, ← s.square.w, ← Category.assoc, Over.w x.val]
  exact pullback.condition.symm

/-- Descent of every compatible local section. -/
def fppfSectionDesc {U : Over B} (x : sectionSubgroup (D := D) U) : U ⟶ s.obj :=
  Over.homMk (s.fppfSectionDescLeft x) (s.fppfSectionDescLeft_over x)

@[simp] theorem localSection_fppfSectionDesc {U : Over B} (x : sectionSubgroup (D := D) U) :
    s.localSection (s.fppfSectionDesc x) = x.val := by
  apply Over.OverMorphism.ext
  apply s.square.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · rw [s.localSection_proj]
    exact s.fppfSectionDescLeft_fac x

/-- The descended scheme represents the compatible local sections. -/
def fppfSectionEquiv (U : Over B) : (U ⟶ s.obj) ≃ sectionSubgroup (D := D) U where
  toFun f := ⟨s.localSection f, s.localSection_mem f⟩
  invFun := s.fppfSectionDesc
  left_inv _f := s.fppfLocalSection_injective U (s.localSection_fppfSectionDesc _)
  right_inv x := Subtype.ext (s.localSection_fppfSectionDesc x)

end SchemeSolution
end Langlands.GroupScheme.Descent
