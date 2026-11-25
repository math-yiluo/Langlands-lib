/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward identifies the successor finite sum with the old sum and one
additional summand.
Source: Stacks Project, Tag 01YF, finite-sum comparison in the successor step.
(blueprint: new-pushforward-fin-sum-succ-iso)
-/
theorem pushforward_fin_sum_succ_iso
    {X Z : Scheme.{u}} (i : Z ⟶ X) (r : ℕ) (I : Z.IdealSheafData) :
    Nonempty ((pushforward i).obj (∐ fun _ : Fin (r + 1) => I.toModules) ≅
      (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⊞
        (pushforward i).obj I.toModules) := by
  let A : Fin (r + 1) → Z.Modules := fun _ ↦ I.toModules
  let B : Fin r → Z.Modules := fun _ ↦ I.toModules
  let e : (∐ A) ≅ (∐ B) ⊞ I.toModules :=
    { hom := Sigma.desc (Fin.cases biprod.inr (fun j ↦ Sigma.ι B j ≫ biprod.inl))
      inv := biprod.desc (Sigma.desc fun j ↦ Sigma.ι A j.succ) (Sigma.ι A 0)
      hom_inv_id := by
        apply Sigma.hom_ext
        intro j
        cases j using Fin.cases with
        | zero => simp [A, B]
        | succ j => simp [A, B]
      inv_hom_id := by
        apply biprod.hom_ext'
        · apply Sigma.hom_ext
          intro j
          simp [A, B]
        · simp [A, B] }
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (pushforward i)
  exact ⟨(pushforward i).mapIso e ≪≫ (pushforward i).mapBiprod (∐ B) I.toModules⟩

end AlgebraicGeometry.Scheme.Modules
