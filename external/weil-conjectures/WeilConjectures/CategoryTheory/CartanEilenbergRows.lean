/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Compatible rows for the Cartan--Eilenberg construction

Source: Stacks Project, Derived Categories, Lemma 015I, alternating short exact rows
(blueprint: def-sp-cartan-eilenberg-rows).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- Two alternating short exact rows, with their compatible augmentations.
These are genuine diagram data, with no injectivity or quasi-isomorphism assumptions.
Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: def-sp-cartan-eilenberg-rows). -/
structure CartanEilenbergRows {C : Type u} [Category.{v} C] [Abelian C]
    (S : CochainComplex C ℤ) where
  A : ℤ → C
  Z : ℤ → C
  D : ℤ → C
  H : ℤ → C
  u : ∀ p, Z p ⟶ A p
  v : ∀ p, A p ⟶ D (p + 1)
  w : ∀ p, D p ⟶ Z p
  x : ∀ p, Z p ⟶ H p
  uv : ∀ p, u p ≫ v p = 0
  wx : ∀ p, w p ≫ x p = 0
  exact₁ : ∀ p, (ShortComplex.mk (u p) (v p) (uv p)).ShortExact
  exact₂ : ∀ p, (ShortComplex.mk (w p) (x p) (wx p)).ShortExact
  jA : ∀ p, S.X p ⟶ A p
  jZ : ∀ p, S.cycles p ⟶ Z p
  jD : ∀ p, image (S.d (p - 1) p) ⟶ D p
  jH : ∀ p, S.homology p ⟶ H p
  comm : ∀ p, jA p ≫ v p ≫ w (p + 1) ≫ u (p + 1) =
    S.d p (p + 1) ≫ jA (p + 1)
  commZ : ∀ p, S.iCycles p ≫ jA p = jZ p ≫ u p
  commD : ∀ p, image.ι (S.d (p - 1) p) ≫ jA p = jD p ≫ w p ≫ u p
  commH : ∀ p, S.homologyπ p ≫ jH p = jZ p ≫ x p

namespace CartanEilenbergRows

variable {C : Type u} [Category.{v} C] [Abelian C] {S : CochainComplex C ℤ}

/-- The horizontal differential is the composite through the boundary and cycle rows.
Source: Stacks Project, Derived Categories, Lemma 015I, last paragraph
(blueprint: def-sp-cartan-eilenberg-rows). -/
noncomputable def complex (R : CartanEilenbergRows S) : CochainComplex C ℤ where
  X := R.A
  d p q := if h : p + 1 = q then
    R.v p ≫ eqToHom (congrArg R.D h) ≫ R.w q ≫ R.u q else 0
  shape p q h := by
    change ¬ p + 1 = q at h
    simp [h]
  d_comp_d' p q r hpq hqr := by
    change p + 1 = q at hpq
    change q + 1 = r at hqr
    subst q
    subst r
    simp [Category.assoc, reassoc_of% (R.uv (p + 1))]

/-- In adjacent degrees the differential is the prescribed composite. 
(blueprint: def-sp-cartan-eilenberg-rows)
-/
@[simp] theorem complex_d (R : CartanEilenbergRows S) (p : ℤ) :
    R.complex.d p (p + 1) = R.v p ≫ R.w (p + 1) ≫ R.u (p + 1) := by
  simp [complex]

/-- The row augmentations form a morphism of complexes.
Source: Stacks Project, Derived Categories, Lemma 015I, last paragraph
(blueprint: def-sp-cartan-eilenberg-rows). -/
noncomputable def augmentation (R : CartanEilenbergRows S) : S ⟶ R.complex where
  f := R.jA
  comm' p q hpq := by
    change p + 1 = q at hpq
    subst q
    simpa using R.comm p

end CartanEilenbergRows
end CategoryTheory
