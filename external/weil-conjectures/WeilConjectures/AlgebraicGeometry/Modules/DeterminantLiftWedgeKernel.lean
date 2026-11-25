/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor

/-!
# The wedge of lifts annihilates the quotient kernel
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The wedge map on the sheaf of lifts annihilates the exterior quotient kernel. -/
theorem determinant_liftWedge_kernel_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶
      exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        tmulSection (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃)
          (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₃) (r := r₃) (U := U) (fun i ↦ S.g.val.app (op U) (c i)))) :
    ∃ w : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶ exteriorPower S.X₂ r₂,
      kernel.ι q ≫ w = 0 ∧ ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (c : Fin r₃ → S.X₂.val.obj (op U)),
        w.val.app (op U)
            (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
              (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  obtain ⟨w, hw⟩ := exteriorSheaf_wedgeMap_exists S.f r₁ r₃ r₂ hr
  obtain ⟨φ, hφ⟩ := determinant_wedge_quotient_factor S hS r₁ r₂ r₃ hr q w hq hw
  refine ⟨w, ?_, hw⟩
  rw [← hφ, ← Category.assoc, kernel.condition, zero_comp]

end AlgebraicGeometry.Scheme.Modules
