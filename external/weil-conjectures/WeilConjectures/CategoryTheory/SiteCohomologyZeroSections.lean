/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData

/-! # Evaluation of degree-zero object cohomology
Source: Mathlib, SheafCohomology/Basic, Ext/Basic, Sheafification and Yoneda.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace CategoryTheory

/-- Degree-zero evaluation `Sheaf.objectCohomologyEval₀` on the identity generator of the free
sheaf is injective, preserves zero, and is natural in the sheaf.
Source: Mathlib, SheafCohomology/Basic, Ext/Basic, Sheafification and Yoneda.
(blueprint: lem-weil-pbc-object-cohomology-zero-evaluation).

Proof: Ext in degree zero is additively equivalent to Hom. The sheafification
adjunction identifies Hom from the free sheaf with natural transformations from
its free representable presheaf. The free-forgetful adjunction then identifies
these with maps from the representable to the underlying presheaf. Yoneda
identifies such maps with sections at X, by evaluation on the identity. All
three identifications preserve zero. Postcomposition with a sheaf morphism
commutes with each identification, proving the displayed naturality equation.
-/
theorem siteCohomology_zero_section_properties
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasExt.{u} (Sheaf T AddCommGrpCat.{u})] :
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      Function.Injective (Sheaf.objectCohomologyEval₀ T X A)) ∧
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      Sheaf.objectCohomologyEval₀ T X A 0 = 0) ∧
    (∀ (A B : Sheaf T AddCommGrpCat.{u}) (f : A ⟶ B) (X : C)
      (x : Sheaf.H' A 0 X),
      Sheaf.objectCohomologyEval₀ T X B
          ((((Sheaf.cohomologyPresheafFunctor T 0).map f).app (op X)).hom x) =
        (f.hom.app (op X)).hom (Sheaf.objectCohomologyEval₀ T X A x)) := by
  refine ⟨fun A X ↦ Sheaf.objectCohomologyEval₀_injective T X A, fun A X ↦ ?_,
    fun A B f X x ↦ Sheaf.objectCohomologyEval₀_naturality T X f x⟩
  unfold Sheaf.objectCohomologyEval₀
  rw [map_zero]
  rfl

end CategoryTheory
