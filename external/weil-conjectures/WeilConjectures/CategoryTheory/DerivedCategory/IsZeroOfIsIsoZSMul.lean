/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Objects of a derived category on which an integer acts invertibly

In the derived category of an abelian category on which an integer `m` acts by zero, an object on
which `m` acts invertibly is zero (`DerivedCategory.isZero_of_isIso_zsmul_id`).
-/

@[expose] public section

open CategoryTheory Limits


/-- In the derived category of an abelian category on which an integer `m` acts by zero, an object
on which `m` acts invertibly is zero: so are all its homology objects. -/
lemma DerivedCategory.isZero_of_isIso_zsmul_id {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {m : ℤ} (hm : ∀ M : A, m • 𝟙 M = 0) {K : DerivedCategory A}
    (h : IsIso (m • 𝟙 K)) : IsZero K := by
  suffices IsIso (0 : K ⟶ K) from IsZero.of_mono_zero K K
  rw [DerivedCategory.isIso_iff]
  intro i
  have : IsIso ((DerivedCategory.homologyFunctor A i).map (m • 𝟙 K)) := inferInstance
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id, hm] at this
  have hz : IsZero ((DerivedCategory.homologyFunctor A i).obj K) :=
    IsZero.of_mono_zero _ ((DerivedCategory.homologyFunctor A i).obj K)
  exact hz.isIso hz _
