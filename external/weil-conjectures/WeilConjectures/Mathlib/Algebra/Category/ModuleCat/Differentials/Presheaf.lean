/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# Postcomposition of derivations of presheaves of modules

Postcomposition of a derivation with a composite of morphisms of presheaves of modules is
iterated postcomposition, and the morphism out of a universal derivation is natural in the
target: `desc d' ≫ f = desc (d'.postcomp f)`.
-/

@[expose] public section

universe v u v₁ v₂ u₁ u₂

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

export PresheafOfModulesOfCommRing (Derivation)

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {M N P : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} {φ : S ⟶ F.op ⋙ R}

namespace Derivation

lemma postcomp_comp (d : M.Derivation φ) (f : M ⟶ N) (g : N ⟶ P) :
    d.postcomp (f ≫ g) = (d.postcomp f).postcomp g := by
  ext X a
  simp

lemma Universal.desc_comp {d : M.Derivation φ} (hd : d.Universal) (d' : N.Derivation φ)
    (f : N ⟶ P) : hd.desc d' ≫ f = hd.desc (d'.postcomp f) :=
  hd.postcomp_injective _ _ (by rw [postcomp_comp, hd.fac, hd.fac])

end Derivation

end PresheafOfModules
