/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Local lifting from an epimorphic comparison to a cycle pullback

Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A compatible pair factors through the kernel-pullback. Pulling back an epimorphic
comparison to that pullback gives a simultaneous lift of its two components.
Source: Stacks Project, Derived Categories, Lemma 05T7 (1), local lifting step
(blueprint: lem-pc-functorial-cycle-pullback-lifting-stage3). -/
theorem cyclePullback_lifting_pointwise {A : Type u} [Category.{v} A] [Abelian A]
    {E F : CochainComplex A ℤ} (ε : E ⟶ F) (i : ℤ)
    (e : E.X i ⟶ pullback (F.d i (i + 1))
      (kernel.ι (E.d (i + 1) (i + 1 + 1)) ≫ ε.f (i + 1)))
    [Epi e]
    (he₁ : e ≫ pullback.fst _ _ = ε.f i)
    (he₂ : e ≫ pullback.snd _ _ ≫ kernel.ι _ = E.d i (i + 1))
    (B : A) (x : B ⟶ E.X (i + 1)) (y : B ⟶ F.X i)
    (hx : x ≫ E.d (i + 1) (i + 1 + 1) = 0)
    (hy : x ≫ ε.f (i + 1) = y ≫ F.d i (i + 1)) :
    ∃ (B' : A) (p : B' ⟶ B) (_ : Epi p) (z : B' ⟶ E.X i),
      z ≫ ε.f i = p ≫ y ∧ z ≫ E.d i (i + 1) = p ≫ x := by
  let d := E.d (i + 1) (i + 1 + 1)
  let f := F.d i (i + 1)
  let g := kernel.ι d ≫ ε.f (i + 1)
  let k : B ⟶ kernel d := kernel.lift d x hx
  have hk : k ≫ kernel.ι d = x := kernel.lift_ι d x hx
  have hw : y ≫ f = k ≫ g := by
    dsimp [g]
    rw [← Category.assoc, hk]
    exact hy.symm
  let a : B ⟶ pullback f g := pullback.lift y k hw
  let p : pullback e a ⟶ B := pullback.snd e a
  let z : pullback e a ⟶ E.X i := pullback.fst e a
  have hz : z ≫ e = p ≫ a := pullback.condition
  refine ⟨pullback e a, p, inferInstance, z, ?_, ?_⟩
  · rw [← he₁, ← Category.assoc, hz, Category.assoc]
    dsimp [a]
    rw [pullback.lift_fst]
  · rw [← he₂, ← Category.assoc, hz, Category.assoc]
    dsimp [a]
    rw [pullback.lift_snd_assoc, hk]

end CochainComplex
