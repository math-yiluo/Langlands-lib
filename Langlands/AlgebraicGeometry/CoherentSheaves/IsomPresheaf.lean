import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.CategoryTheory.Sites.PseudofunctorHomLift

/-! # The actual Isom presheaf of two coherent families -/

noncomputable section

universe u w v v' c a

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private lemma lifted_pullHom_down {C : Type c} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', a})
    {T₁ T₂ Y Y' : C}
    {M : F.obj (.mk (op T₁))} {N : F.obj (.mk (op T₂))}
    {h₁ : Y ⟶ T₁} {h₂ : Y ⟶ T₂}
    (b : ((Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{w} F).map
        h₁.op.toLoc).toFunctor.obj (ULiftHom.objUp.{a, w} M) ⟶
      ((Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{w} F).map
        h₂.op.toLoc).toFunctor.obj (ULiftHom.objUp.{a, w} N))
    (g : Y' ⟶ Y) (gh₁ : Y' ⟶ T₁) (gh₂ : Y' ⟶ T₂)
    (e₁ : g ≫ h₁ = gh₁) (e₂ : g ≫ h₂ = gh₂) :
    (pullHom b g gh₁ gh₂ e₁ e₂).down =
      pullHom (F := F) b.down g gh₁ gh₂ e₁ e₂ := by
  subst gh₁ gh₂
  dsimp [pullHom]
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

private def presheafHomLiftIso {C : Type c} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', a})
    {B : C} (M N : F.obj (.mk (op B))) :
    (Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{w} F).presheafHom
        (ULiftHom.objUp.{a, w} M) (ULiftHom.objUp.{a, w} N) ≅
      F.presheafHom M N ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro b
    apply ULift.ext
    exact lifted_pullHom_down F b q.unop.left Z'.unop.hom Z'.unop.hom
      q.unop.w q.unop.w)

variable {S X : Scheme.{u}} (f : X ⟶ S) {T : Over S}

/-- The actual map to `T` associated to an arbitrary scheme over `T.left`. -/
abbrev testMap (T : Over S) (Z : Over T.left) :
    (Over.map T.hom).obj Z ⟶ T :=
  (T.iteratedSliceBackward.obj Z).hom

/-- Actual isomorphisms between the ordinary pullbacks of two families,
on the entire slice of schemes over the underlying test scheme. -/
def isomPresheaf (M N : FamilyGroupoid f T) : AlgebraicSpace.Presheaf T.left :=
  T.iteratedSliceBackward.op ⋙
    (Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{u + 1}
      (pseudofunctor f)).presheafHom
      (ULiftHom.objUp.{u + 1, u + 1} M) (ULiftHom.objUp.{u + 1, u + 1} N)

/-- Each point is precisely a lifted actual module isomorphism. -/
def isomPointsEquiv (M N : FamilyGroupoid f T) (Z : Over T.left) :
    (isomPresheaf f M N).obj (op Z) ≃
      ULift.{u + 1}
        (((pullback f (testMap T Z)).obj M).of.obj ≅
          ((pullback f (testMap T Z)).obj N).of.obj) where
  toFun a := ULift.up (homEquiv f _ a.down)
  invFun e := ULift.up ((homEquiv f _).symm e.down)
  left_inv a := by
    apply ULift.ext
    exact (homEquiv f _).symm_apply_apply a.down
  right_inv e := by
    apply ULift.ext
    exact (homEquiv f _).apply_symm_apply e.down

/-- A natural comparison with the explicit lift of the original presheaf of
family-groupoid arrows, including every restriction map. -/
def isomPresheafLiftIso (M N : FamilyGroupoid f T) :
    isomPresheaf f M N ≅
      T.iteratedSliceBackward.op ⋙
        ((pseudofunctor f).presheafHom M N ⋙ uliftFunctor.{u + 1}) :=
  Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (presheafHomLiftIso.{u + 1} (pseudofunctor f) M N)

end Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid
