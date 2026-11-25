/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
/-! Constant quotient component of constant coefficient completion.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node).
(auxiliary; not a blueprint node)
The finite constant quotient map is sectionwise surjective and has kernel generated
by the constant sections of the corresponding power of the ideal. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]

private theorem constantRing_surjective {A B : CommRingCat.{u}} (f : A ⟶ B)
    (hf : Function.Surjective f) (J : GrothendieckTopology C) (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J CommRingCat.{u}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app B ≫ s ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s ≫
      (constantSheaf J (Type u)).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s, hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  exact ⟨r.hom.app U x, congrArg (fun h ↦ h.hom.app U x) hr⟩

theorem flat_and_quotients_quotient (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∀ (n : ℕ) (U : C),
      Function.Surjective ((quotient J A I n).hom.app (op U)) ∧
      RingHom.ker ((quotient J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
      (constantSection (J := J) (a : A)).val (op U))) := by
  intro n U
  constructor
  · apply constantRing_surjective
    exact Ideal.Quotient.mk_surjective
  · exact constant_quotient_kernel J A I n U
end CategoryTheory.ConstantCompletion
