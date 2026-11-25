/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex

import WeilConjectures.AlgebraicGeometry.Modules.ComplementaryBlockResidueVanishes
import WeilConjectures.AlgebraicGeometry.Modules.FreeMapResidueDetection

/-! # Vanishing of the complementary block on a reduced scheme
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A block diagonal form with an invertible a by a pivot has zero complementary
block if its field-valued fibre ranks are at most a on a reduced scheme. -/
theorem complementary_block_eq_zero_of_rank_le
    {Y Z : Scheme.{u}} [IsReduced Y] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (U : Z.Opens)
    (hrank : ∀ z : Z, z ∈ U →
      ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
        Set.range g.base = {j.base z} ∧
        ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank ≤ a)
    (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
    (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a))))
    (f : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin a)) ⟶
      free (ULift.{u} (Fin a))) [IsIso f]
    (δ : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (m - a))) ⟶
      free (ULift.{u} (Fin (n - a))))
    (hform : (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
      eS.hom ≫ biprod.map f δ ≫ eT.inv) : δ = 0 := by
  let : IsReduced Z := isReduced_of_isOpenImmersion j
  apply free_map_eq_zero_of_residue_evaluations
  intro x
  exact complementary_block_residue_eq_zero_of_rank_le eM eN φ j a U eS eT f δ
    hform x (hrank x.1 x.2)

end AlgebraicGeometry.Scheme.Modules
