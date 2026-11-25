/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Multiplication by a scalar on a sheaf of modules

For a sheaf `M` of modules over a commutative ring `R` and `c ∈ R`, multiplication by `c` is an
endomorphism `CategoryTheory.Sheaf.smulEnd M c : M ⟶ M`, commuting with every morphism of
sheaves, and acting on global sections by multiplication by `c`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [CommRing R]

/-- Multiplication by a scalar `c` on a sheaf of `R`-modules. -/
@[simps]
noncomputable def smulEnd (M : Sheaf J (ModuleCat.{w} R)) (c : R) : M ⟶ M where
  hom :=
    { app U := c • 𝟙 _
      naturality U V f := by simp }

lemma smulEnd_comp {M N : Sheaf J (ModuleCat.{w} R)} (c : R) (φ : M ⟶ N) :
    smulEnd M c ≫ φ = φ ≫ smulEnd N c := by
  ext U x
  simp

/-- On global sections, multiplication by `c` is multiplication by `c`. -/
lemma Γ_map_smulEnd [HasWeakSheafify J (ModuleCat.{w} R)] [HasTerminal C]
    [HasGlobalSectionsFunctor J (ModuleCat.{w} R)] {T : C} (hT : IsTerminal T)
    (M : Sheaf J (ModuleCat.{w} R)) (c : R) (x : (Sheaf.Γ J (ModuleCat.{w} R)).obj M) :
    (Sheaf.Γ J (ModuleCat.{w} R)).map (smulEnd M c) x = c • x := by
  have h := ConcreteCategory.congr_hom
    ((Sheaf.ΓNatIsoSheafSections J (ModuleCat.{w} R) hT).hom.naturality (smulEnd M c)) x
  apply ((Sheaf.ΓNatIsoSheafSections J (ModuleCat.{w} R) hT).app M).toLinearEquiv.injective
  simp only [Iso.toLinearEquiv_apply, Iso.app_hom, map_smul]
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  simp

end CategoryTheory.Sheaf
