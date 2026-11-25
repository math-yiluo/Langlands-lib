/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Additive section fractions on an ambient open

Source: Stacks Project, Tags 09MR and 01PW, the presentation by fractions.
(blueprint: def-sc-open-section-fraction-presentation).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- The additive relations for section fractions on an arbitrary ambient open.
Source: Stacks Project, Tags 09MR and 01PW.
(blueprint: def-sc-open-section-fraction-presentation). -/
noncomputable def openSectionFractionRelations {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) :
    AddSubgroup (⨁ n : ℕ, Γ(F ⊗ L.tensorPow n, U)) :=
  AddSubgroup.closure {z | ∃ (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
    z = DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, U)) n t -
      DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, U)) (n + b)
        ((mulTensorPowSection (homOfGlobalSection L s) F n b).app U t)}

/-- Additive degree-zero section fractions over `U`, with all fraction relations retained.
Source: Stacks Project, Tags 09MR and 01PW.
(blueprint: def-sc-open-section-fraction-presentation). -/
noncomputable abbrev OpenSectionFractionPresentation {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) : Type u :=
  (⨁ n : ℕ, Γ(F ⊗ L.tensorPow n, U)) ⧸ openSectionFractionRelations L F s U

/-- The section fraction represented by the numerator `t` in degree `n`.
Source: Stacks Project, Tags 09MR and 01PW.
(blueprint: def-sc-open-section-fraction-presentation). -/
noncomputable def openSectionFraction {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)) :
    OpenSectionFractionPresentation L F s U :=
  QuotientAddGroup.mk (DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, U)) n t)

end AlgebraicGeometry.Scheme.Modules
