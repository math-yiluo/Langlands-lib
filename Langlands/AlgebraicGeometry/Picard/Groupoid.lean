import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Picard.RelativeGeometry
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # The groupoid of actual line bundles and its pullback pseudofunctor -/

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- Actual line bundles, with only their isomorphisms as arrows. -/
abbrev PicardGroupoid (X : Scheme.{u}) := Core (LineBundle X)

namespace PicardGroupoid

private lemma core_eqToHom {C : Type*} [Category* C] {A B : Core C} (e : A = B) :
    (eqToHom e).iso.hom = eqToHom (congrArg Core.of e) := by
  cases e
  rfl

variable {W X Y Z : Scheme.{u}}

/-- Ordinary pullback on the groupoids of line bundles. -/
def pullback (f : X ⟶ Y) : PicardGroupoid Y ⥤ PicardGroupoid X :=
  (LineBundle.pullback f).core

/-- Identity comparison induced by the usual module pullback comparison. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (PicardGroupoid X) :=
  (LineBundle.pullbackId X).core

/-- Composition comparison induced by the usual module pullback comparison. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  (LineBundle.pullbackComp f g).core

set_option backward.isDefEq.respectTransparency false in
lemma pullback_associativity (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
    eqToHom (by simp) := by
  apply NatTrans.ext
  funext L
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  simpa [pullback, pullbackComp, LineBundle.pullback, LineBundle.pullbackComp,
    Functor.core, Core.functorToCore, Core.inclusion, ObjectProperty.lift,
    LineBundle.forget, eqToHom_app, core_eqToHom] using
    congrArg (fun η ↦ η.app L.of.obj) (Scheme.Modules.pseudofunctor_associativity f g h)

set_option backward.isDefEq.respectTransparency false in
lemma pullback_left_unitality (f : X ⟶ Y) :
    (pullbackComp f (𝟙 Y)).inv ≫
      Functor.whiskerRight (pullbackId Y).hom (pullback f) ≫ (Functor.leftUnitor _).hom =
        eqToHom (by simp) := by
  apply NatTrans.ext
  funext L
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  simpa [pullback, pullbackComp, pullbackId, LineBundle.pullback,
    LineBundle.pullbackComp, LineBundle.pullbackId,
    Functor.core, Core.functorToCore, Core.inclusion, ObjectProperty.lift,
    LineBundle.forget, eqToHom_app, core_eqToHom] using
    congrArg (fun η ↦ η.app L.of.obj) (Scheme.Modules.pseudofunctor_left_unitality f)

set_option backward.isDefEq.respectTransparency false in
lemma pullback_right_unitality (f : X ⟶ Y) :
    (pullbackComp (𝟙 X) f).inv ≫
      Functor.whiskerLeft (pullback f) (pullbackId X).hom ≫ (Functor.rightUnitor _).hom =
        eqToHom (by simp) := by
  apply NatTrans.ext
  funext L
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  simpa [pullback, pullbackComp, pullbackId, LineBundle.pullback,
    LineBundle.pullbackComp, LineBundle.pullbackId,
    Functor.core, Core.functorToCore, Core.inclusion, ObjectProperty.lift,
    LineBundle.forget, eqToHom_app, core_eqToHom] using
    congrArg (fun η ↦ η.app L.of.obj) (Scheme.Modules.pseudofunctor_right_unitality f)

/-- The contravariant pseudofunctor of actual line-bundle groupoids on schemes. -/
def pseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (PicardGroupoid X.unop))
    (fun f ↦ (pullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (pullbackId X.unop))
    (fun f g ↦ Cat.Hom.isoMk (pullbackComp g.unop f.unop).symm)
    (fun f g h ↦ by
      apply Cat.Hom₂.ext
      exact pullback_associativity h.unop g.unop f.unop)
    (fun f ↦ by
      apply Cat.Hom₂.ext
      exact pullback_left_unitality f.unop)
    (fun f ↦ by
      apply Cat.Hom₂.ext
      exact pullback_right_unitality f.unop)

/-- The relative pseudofunctor has the actual groupoid on each fibre product. -/
def relative {S X : Scheme.{u}} (f : X ⟶ S) :
    LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat :=
  (relativeSpace f).op.toPseudofunctor.comp pseudofunctor

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
