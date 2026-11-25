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
import WeilConjectures.AlgebraicGeometry.Modules.Determinant
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExactExists
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt

/-!
# Determinants in short exact sequences
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Determinant lines are invertible and multiplicative, with the canonical isomorphism
characterized on wedges on every open subset. The inverse sends a tensor of wedges to the
wedge of the included sections followed by any lifts of the quotient sections. Since it is
a morphism of sheaves, it commutes with restriction; its characterization uses every open. -/
theorem determinant_shortExact {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    (exteriorPower S.X₁ r₁).IsInvertible ∧
    (exteriorPower S.X₂ r₂).IsInvertible ∧
    (exteriorPower S.X₃ r₃).IsInvertible ∧
    ∃! e : exteriorPower S.X₂ r₂ ≅ exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i => Fin.append (fun j => S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨e, he⟩ := determinant_shortExact_exists S hS r₁ r₂ r₃ hr
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  have := hS.epi_g
  apply exteriorTensor_lift_hom_ext S.g r₁ r₃
  intro U a c
  exact (he' U a (fun i ↦ S.g.val.app (op U) (c i)) c (fun _ ↦ rfl)).trans
    (he U a (fun i ↦ S.g.val.app (op U) (c i)) c (fun _ ↦ rfl)).symm

end AlgebraicGeometry.Scheme.Modules
