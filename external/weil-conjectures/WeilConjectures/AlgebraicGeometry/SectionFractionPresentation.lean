/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Defs

/-! # Fractions of tensor-power sections

Source: Stacks Project, Properties, Section 0B5K, equation module-invert-s (Tag 0B5L)
(blueprint: def-sc-section-fraction-presentation).

This is the generators-and-relations presentation of the degree-zero localization:
`[n,t]` represents `t/s^n`, and `[n,t] = [n+b,t ⊗ s^b]`.
Only nonnegative twists occur in degree-zero fractions, even when the numerator module
is graded by all integers. Addition and scalar multiplication are the quotient operations.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- The relations identifying a fraction with the same fraction after multiplying numerator
and denominator by a power of the global section `s` (as the morphism
`homOfGlobalSection L s : 𝒪_X ⟶ L`). Source: Stacks Project, Properties, Section 0B5K,
equation module-invert-s (blueprint: def-sc-section-fraction-presentation). -/
noncomputable def sectionFractionRelations {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) :
    Submodule Γ(X, ⊤) (⨁ n : ℕ, Γ(F ⊗ L.tensorPow n, ⊤)) :=
  Submodule.span Γ(X, ⊤) {z | ∃ (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)),
    z = DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, ⊤)) n t -
      DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, ⊤)) (n + b)
        ((mulTensorPowSection (homOfGlobalSection L s) F n b).app ⊤ t)}

/-- The module of degree-zero section fractions, presented as the direct sum of nonnegative
numerator degrees modulo the fraction relations. Source: Stacks Project, Properties,
Section 0B5K, equation module-invert-s (blueprint: def-sc-section-fraction-presentation). -/
noncomputable abbrev SectionFractionPresentation {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) : Type u :=
  (⨁ n : ℕ, Γ(F ⊗ L.tensorPow n, ⊤)) ⧸ sectionFractionRelations L F s

/-- The fraction `t/s^n`. Source: Stacks Project, Properties, Section 0B5K,
equation module-invert-s (blueprint: def-sc-section-fraction-presentation). -/
noncomputable def sectionFraction {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)) :
    SectionFractionPresentation L F s :=
  Submodule.Quotient.mk (DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, ⊤)) n t)

end AlgebraicGeometry.Scheme.Modules
