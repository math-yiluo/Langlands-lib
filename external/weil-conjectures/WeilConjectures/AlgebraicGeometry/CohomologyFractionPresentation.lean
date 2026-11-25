/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Degree-zero fractions of twisted module cohomology

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, equation preceding the lemma
(blueprint: def-sc-cohomology-fraction-presentation).

The underlying additive group of the degree-zero homogeneous localization has the
presentation with generators `[n, ξ]` and relations `[n, ξ] = [n+b, s^b ξ]`.
Only nonnegative numerator degrees enter degree-zero fractions, even though the full
cohomology module is graded by integers. The quotient retains all torsion relations.
-/

@[expose] public section

universe uCF

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- The fraction relations on twisted cohomology over an open `U`.
Source: Stacks, Lemma 09MR, degree-zero fractions ξ/s^n
(blueprint: def-sc-cohomology-fraction-presentation). -/
noncomputable def cohomologyFractionRelations {X : Scheme.{uCF}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (U : X.Opens) :
    AddSubgroup (⨁ n : ℕ,
      (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow n : X.Modules)) :=
  AddSubgroup.closure {z | ∃ (n b : ℕ)
    (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
      (F ⊗ L.tensorPow n : X.Modules)),
    z = DirectSum.of (fun i : ℕ ↦
        (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow i : X.Modules))
        n ξ -
      DirectSum.of (fun i : ℕ ↦
        (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow i : X.Modules))
        (n + b) ((RingedSpace.openModuleCohomology X.toRingedSpace p U).map
          (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ)}

/-- The underlying additive group of H^p_*(U,L,F)_(s), with its explicit fraction relations.
Source: Stacks, Lemma 09MR, degree-zero localization
(blueprint: def-sc-cohomology-fraction-presentation). -/
noncomputable abbrev CohomologyFractionPresentation {X : Scheme.{uCF}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (U : X.Opens) : Type uCF :=
  (⨁ n : ℕ,
    (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow n : X.Modules)) ⧸
      cohomologyFractionRelations L F s p U

/-- The class ξ/s^n in the degree-zero localization.
Source: Stacks, Lemma 09MR, fraction formula
(blueprint: def-sc-cohomology-fraction-presentation). -/
noncomputable def cohomologyFraction {X : Scheme.{uCF}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (U : X.Opens) (n : ℕ)
    (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
      (F ⊗ L.tensorPow n : X.Modules)) : CohomologyFractionPresentation L F s p U :=
  QuotientAddGroup.mk (DirectSum.of (fun i : ℕ ↦
    (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj (F ⊗ L.tensorPow i : X.Modules)) n ξ)

end AlgebraicGeometry.Scheme.Modules
