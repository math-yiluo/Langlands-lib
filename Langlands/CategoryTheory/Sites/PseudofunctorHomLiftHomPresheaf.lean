import Langlands.CategoryTheory.Sites.PseudofunctorHomLift

/-! # Hom presheaves and explicit morphism-universe lifts -/

noncomputable section

universe w v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

namespace Langlands.CategoryTheory.PseudofunctorHomLift

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- Lowering an explicitly lifted morphism commutes with coherent pullback. -/
lemma pullHom_down {T₁ T₂ Y Y' : C}
    {M : F.obj (.mk (op T₁))} {N : F.obj (.mk (op T₂))}
    {h₁ : Y ⟶ T₁} {h₂ : Y ⟶ T₂}
    (b : ((homLift.{w} F).map h₁.op.toLoc).toFunctor.obj
        (ULiftHom.objUp.{u', w} M) ⟶
      ((homLift.{w} F).map h₂.op.toLoc).toFunctor.obj
        (ULiftHom.objUp.{u', w} N))
    (g : Y' ⟶ Y) (gh₁ : Y' ⟶ T₁) (gh₂ : Y' ⟶ T₂)
    (e₁ : g ≫ h₁ = gh₁) (e₂ : g ≫ h₂ = gh₂) :
    (pullHom b g gh₁ gh₂ e₁ e₂).down =
      pullHom (F := F) b.down g gh₁ gh₂ e₁ e₂ := by
  subst gh₁ gh₂
  dsimp [pullHom]
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- Lifting fibre morphisms gives the explicit value lift of the original
Hom presheaf, naturally on the full slice. -/
def presheafHomIso {B : C} (M N : F.obj (.mk (op B))) :
    (homLift.{w} F).presheafHom
        (ULiftHom.objUp.{u', w} M) (ULiftHom.objUp.{u', w} N) ≅
      F.presheafHom M N ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro b
    apply ULift.ext
    exact pullHom_down F b q.unop.left Z'.unop.hom Z'.unop.hom
      q.unop.w q.unop.w)

end Langlands.CategoryTheory.PseudofunctorHomLift
