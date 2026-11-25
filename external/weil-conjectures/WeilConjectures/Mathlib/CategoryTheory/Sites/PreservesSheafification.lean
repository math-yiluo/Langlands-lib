/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Sheafification of presheaves of rings and of their underlying presheaves of sets

If the forgetful functor `CommRingCat ⥤ Type _` preserves sheafification (as it does on any
site, by the plus construction), then the underlying presheaf of sets of the sheafification
`P⁺` of a presheaf of commutative rings `P` is a sheaf of sets, and the underlying map of the
canonical map `P ⟶ P⁺` is a sheafification of the underlying presheaf of sets of `P`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (forget CommRingCat.{w})]
  [J.PreservesSheafification (forget CommRingCat.{w})]

/-- **The sheafification of a presheaf of rings has as underlying sheaf of sets the
sheafification of sets.** For a presheaf `P` of commutative rings, the underlying presheaf of
sets of its sheafification `P⁺` is a sheaf, and `P ⟶ P⁺` is, on underlying presheaves of sets,
a sheafification: every morphism of presheaves of sets from the underlying presheaf of `P` to a
sheaf of sets `H` factors uniquely through it. In particular, for a commutative ring `R`, the
underlying sheaf of sets of the constant sheaf of rings `R` is the constant sheaf of sets on
`R`, compatibly with the canonical maps from the constant presheaves.
(blueprint: `lem-weil-pbc-ring-sheafification-underlying-sets`) -/
theorem sheafify_comp_forget_commRingCat_isSheafification (P : Cᵒᵖ ⥤ CommRingCat.{w}) :
    Presheaf.IsSheaf J (sheafify J P ⋙ forget CommRingCat.{w}) ∧
      (∀ (H : Cᵒᵖ ⥤ Type w), Presheaf.IsSheaf J H →
        ∀ f : P ⋙ forget CommRingCat.{w} ⟶ H, ∃! g : sheafify J P ⋙ forget CommRingCat.{w} ⟶ H,
          whiskerRight (toSheafify J P) (forget CommRingCat.{w}) ≫ g = f) ∧
      ∀ R : CommRingCat.{w},
        whiskerRight (toSheafify J ((const Cᵒᵖ).obj R)) (forget CommRingCat.{w}) ≫
            ((constantCommuteCompose J (forget CommRingCat.{w})).hom.app R).hom =
          (constComp Cᵒᵖ R (forget CommRingCat.{w})).hom ≫
            toSheafify J ((const Cᵒᵖ).obj ((forget CommRingCat.{w}).obj R)) := by
  have hP : Presheaf.IsSheaf J (sheafify J P ⋙ forget CommRingCat.{w}) :=
    ((sheafCompose J (forget CommRingCat.{w})).obj ((presheafToSheaf J _).obj P)).property
  refine ⟨hP, fun H hH f ↦ ?_, fun R ↦ ?_⟩
  · refine ⟨(sheafifyComposeIso J (forget CommRingCat.{w}) P).inv ≫ sheafifyLift J f hH,
      by simp, fun g hg ↦ ?_⟩
    rw [Iso.eq_inv_comp]
    apply sheafify_hom_ext J _ _ hH
    simp [hg]
  · rw [constantCommuteCompose_hom_app_hom, sheafComposeIso_inv_fac_assoc, toSheafify_naturality]

end CategoryTheory
