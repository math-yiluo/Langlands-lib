/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Integers vanishing in the coefficient ring act by zero on sheaves of modules
-/

@[expose] public section

namespace CategoryTheory.Sheaf

/-- An integer `m` which vanishes in `R` acts by zero on every sheaf of `R`-modules. -/
lemma zsmul_id_eq_zero_of_intCast_eq_zero {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Type*} [Ring R] {m : ℤ} (hm : (m : R) = 0)
    (M : Sheaf J (ModuleCat R)) : m • 𝟙 M = 0 := by
  ext U x
  have h := congr_arg (fun f ↦ (f.app U).hom x)
    ((sheafToPresheaf J (ModuleCat R)).map_zsmul (f := 𝟙 M) (r := m))
  simpa [← Int.cast_smul_eq_zsmul R, hm] using h

end CategoryTheory.Sheaf
