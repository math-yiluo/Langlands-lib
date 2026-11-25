/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-! # Finite towers of constant extensions

The triangles in the cohomological induction of Stacks Project, Tag 094G,
before choosing chain representatives for their boundary maps.
-/

@[expose] public section

universe u v z w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- A tower starting with a finite constant object in degree `a`, then attaching
finite constant objects in successive higher degrees. A step records the rotated
triangle `K → L → S(M)[-(a+n)] → K[1]`, where `L` has the shorter tower.
No chain complex representing the tower, or chain representative of its boundary,
is part of these data.

Source: Stacks Project, Cohomology on Sites, Tag 094G, the induction through
`lemma-locally-constant`'s triangle, before the last differential is constructed.
(auxiliary; not a blueprint node) -/
inductive FiniteConstantExtensionTower
    {B : Type u} [CommRing B]
    {A : Type z} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (S : ModuleCat.{u} B ⥤ A) (a : ℤ) : ℕ → DerivedCategory A → Prop
  | single (M : ModuleCat.{u} B) (hM : Module.Finite B M)
      (K : DerivedCategory A)
      (e : Nonempty (K ≅ DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor A a).obj (S.obj M)))) :
      FiniteConstantExtensionTower S a 0 K
  | step {n : ℕ} {K L : DerivedCategory A}
      (M : ModuleCat.{u} B) (hM : Module.Finite B M)
      (hL : FiniteConstantExtensionTower S a n L)
      (i : K ⟶ L)
      (δ : L ⟶ DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor A (a + n)).obj (S.obj M)))
      (j : DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor A (a + n)).obj (S.obj M)) ⟶ K⟦(1 : ℤ)⟧)
      (hT : Triangle.mk i δ j ∈ distTriang (DerivedCategory A)) :
      FiniteConstantExtensionTower S a (n + 1) K

end CategoryTheory
