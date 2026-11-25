/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement

/-! # The sheaf-module left unitor on pure sections -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.TwistedActionRingedSite

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}}

private abbrev forgetModules :=
  SheafOfModules.forget (ring S) ⋙ PresheafOfModules.restrictScalars (𝟙 (ring S).obj)

private abbrev tensorAdj := PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)

/-- The left unitor acts by scalar multiplication on a sheafified pure tensor.

Source: Stacks 03EK and 03EL, the tensor unit of module sheaves
(blueprint: lem-sf-sheaf-tensor-pure-left-unit).

Proof: give the forgetful functor to presheaves its lax monoidal structure from the
sheafification adjunction. Its unit map is the identity by the adjunction triangle;
its tensor map on sections is exactly the sheafification-unit pure tensor. Evaluate
its left-unitality equation on the ordinary presheaf tensor r tensor x. The presheaf
left unitor is scalar multiplication, giving the asserted formula. -/
theorem pure_left_unitor (M : Modules S) (X : Dᵒᵖ)
    (r : S.obj.obj X) (x : M.val.obj X) :
    (λ_ M).hom.val.app X (pureTensor (𝟙_ _) M X r x) = r • x := by
  let V := forgetModules (S := S)
  let adj := tensorAdj (S := S)
  let : V.LaxMonoidal := adj.rightAdjointLaxMonoidal
  have he : Functor.LaxMonoidal.ε V = 𝟙 _ := by
    change adj.unit.app _ ≫ V.map (adj.counit.app (𝟙_ (Modules S))) = 𝟙 _
    exact adj.right_triangle_components _
  have hm (A B : Modules S) (a : A.val.obj X) (b : B.val.obj X) :
      (Functor.LaxMonoidal.μ V A B).app X (a ⊗ₜ[S.obj.obj X] b) =
        pureTensor A B X a b := by
    simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
    rfl
  have h := Functor.LaxMonoidal.left_unitality V M
  rw [he, id_whiskerRight, Category.id_comp] at h
  have hh := congrArg (fun f ↦ f.app X (r ⊗ₜ[S.obj.obj X] x)) h
  change r • x = (λ_ M).hom.val.app X
    ((Functor.LaxMonoidal.μ V (𝟙_ _) M).app X (r ⊗ₜ[S.obj.obj X] x)) at hh
  rw [hm] at hh
  exact hh.symm

end CategoryTheory.TwistedActionRingedSite
