import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber
import Mathlib.CategoryTheory.Groupoid

/-! # The presheaf of actual automorphism isomorphisms -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

namespace Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {U : C} (ξ : F.obj (.mk (op U)))

/-- Automorphism isomorphisms of an actual family, on the complete test slice. -/
def automorphismIsoPresheaf : (Over U)ᵒᵖ ⥤ Type v' where
  obj T := (F.map T.unop.hom.op.toLoc).toFunctor.obj ξ ≅
    (F.map T.unop.hom.op.toLoc).toFunctor.obj ξ
  map {T V} g := ↾fun e ↦ pullIso e g.unop.left V.unop.hom V.unop.hom g.unop.w g.unop.w
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro e
    exact pullIso_id e
  map_comp {T V W} g h := by
    apply ConcreteCategory.hom_ext
    intro e
    exact (pullIso_pullIso e g.unop.left V.unop.hom V.unop.hom
      h.unop.left W.unop.hom W.unop.hom g.unop.w g.unop.w h.unop.w h.unop.w).symm

variable [∀ T : C, IsGroupoid (F.obj (.mk (op T)))]

/-- In groupoid fibres, the full endomorphism presheaf retains exactly the
same data as the presheaf of actual automorphism isomorphisms. -/
def presheafHomAutomorphismIso :
    F.presheafHom ξ ξ ≅ automorphismIsoPresheaf F ξ :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    { toFun := fun φ ↦ asIso φ
      invFun := fun e ↦ e.hom
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Iso.ext rfl }) (by
    intro T V g
    apply ConcreteCategory.hom_ext
    intro φ
    apply Iso.ext
    rfl)

end Langlands.CategoryTheory.PseudofunctorPointFiber
