import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Morphism presheaves and precomposition -/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory CategoryTheory.Bicategory Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

namespace Langlands.CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v₃, u₃}) {S : C}
    (M N : F.obj (.mk (op (G.obj S))))

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing a pseudofunctor restricts its full morphism presheaf. -/
def presheafHomPrecompositionIso :
    (G.op.toPseudofunctor.comp F).presheafHom M N ≅
      (Over.post G).op ⋙ F.presheafHom M N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro Z W h
    ext a
    change pullHom (F := G.op.toPseudofunctor.comp F) a h.unop.left
        W.unop.hom W.unop.hom =
      pullHom (F := F) a (G.map h.unop.left) (G.map W.unop.hom)
        (G.map W.unop.hom)
        (by simpa only [Quiver.Hom.unop_op, ← G.map_comp] using congrArg G.map h.unop.w)
        (by simpa only [Quiver.Hom.unop_op, ← G.map_comp] using congrArg G.map h.unop.w)
    dsimp [pullHom, Pseudofunctor.comp,
      Pseudofunctor.mapComp', Functor.toPseudofunctor,
      pseudofunctorOfIsLocallyDiscrete, PrelaxFunctor.comp, PrelaxFunctorStruct.comp,
      Quiver.Hom.toLoc, Prefunctor.comp]
    dsimp only [PrelaxFunctor.mapFunctor]
    simp only [← Category.assoc]
    simp only [← Cat.Hom₂.comp_app, ← F.map₂_comp, eqToHom_trans]
    simp only [Cat.Hom₂.comp_app, Category.assoc]
    simp only [← Cat.Hom₂.comp_app, ← F.map₂_comp, eqToHom_trans])

end Langlands.CategoryTheory
