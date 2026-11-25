/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Finite prime-field filtrations of constructible module sheaves

Source: Stacks Project, Theorem 03SC, second proof paragraph; Lemma 03RZ.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The finite extension closure of constructible module sheaves whose underlying
abelian sheaf is a constructible prime-field sheaf.

This inductive predicate records a finite extension tree, without any cohomological
assertion. A zero object is included as a prime-field factor with zero value.
Source: Stacks Project, Theorem 03SC, second proof paragraph.
(blueprint: theorem-cohomology-curves) -/
inductive HasPrimeFieldFiltration (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) → Prop
  | prime (r : ℕ) [Fact r.Prime]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [IsConstructibleSheaf F]
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
      [IsConstructibleSheaf G]
      (e : (sheafCompose _ (forget₂
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj G ≅
        (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) :
      HasPrimeFieldFiltration Λ X F
  | extension (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hS : S.ShortExact) [IsConstructibleSheaf S.X₁] [IsConstructibleSheaf S.X₃]
      (h₁ : HasPrimeFieldFiltration Λ X S.X₁)
      (h₃ : HasPrimeFieldFiltration Λ X S.X₃) : HasPrimeFieldFiltration Λ X S.X₂

end AlgebraicGeometry.Scheme
