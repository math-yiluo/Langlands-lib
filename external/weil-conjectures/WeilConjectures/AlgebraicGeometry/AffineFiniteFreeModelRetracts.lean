/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelTermIsoFree

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every term of the explicit affine finite-free model is a retract of a finite
free localized structure-sheaf module.
Source: Stacks Project, Tag 068C and Definition 08C4, finite-basis argument
(blueprint: lem-affine-finite-free-model-retracts).

Choose a finite basis of the finite free module `K.X n`, identify its associated
sheaf with `tildeFinsupp`, and transport the inclusion and projection through
the affine-chart restriction and inverse localized-site equivalence. Additivity
preserves the identity composite; rank zero handles zero terms. -/ 
theorem affine_finite_free_model_retracts {Y : Scheme.{u}}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ)
    (hfree : ∀ n, Module.Free (Γ(Y, U) : Type u) (K.X n))
    (hfinite : ∀ n, Module.Finite (Γ(Y, U) : Type u) (K.X n)) :
    ∀ n : ℤ, ∃ m : ℕ,
      ∃ (ι : (affineFiniteFreeModelComplex U hU K).X n ⟶
          SheafOfModules.free
            (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
            (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶
          (affineFiniteFreeModelComplex U hU K).X n),
        ι ≫ π = 𝟙 _ := by
  intro n
  obtain ⟨m, ⟨e⟩⟩ := affine_finite_free_model_term_iso_free U hU K hfree hfinite n
  exact ⟨m, e.hom, e.inv, e.hom_inv_id⟩

end AlgebraicGeometry
