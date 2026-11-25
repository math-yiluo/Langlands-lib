/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Basic

import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerCompletedFreeSurjection
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerFreeKernelCorrection
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Finiteness and reduction of an adic tower limit

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/-- Finite generation and the projection kernel formula for an algebraic adic tower.
This concerns one given completed module and one given limit comparison, and constructs
neither modules, functors nor morphism lifts.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, generator-lifting,
Nakayama, Mittag-Leffler and the final cokernel calculation.
(blueprint: lem-weil-pbc-adic-tower-finite-limit).

Proof: Surjectivity of successive transitions implies surjectivity of every limit
projection by recursive lifting. Lift a finite generating family at level zero to the
limit. At level n the resulting map from a finite free A/I^(n+1)-module is surjective:
its reduction modulo I generates level zero, and I/I^(n+1) is nilpotent, so apply
nilpotent Nakayama. The kernels of these free presentations have surjective transitions.
Indeed lift a kernel vector one level; its image is in I^(n+1) times the next module.
Surjectivity of the presentation supplies a correction vector in I^(n+1) times the
free module; subtract it without changing the preceding coordinate. The exactness
lemma for towers with surjective kernels now gives a surjection from a finite free
completed module onto the limit. The residue equation makes this surjection completed
linear, so N is finite. Fix n. An element in the kernel of the nth projection lifts
to the completed free module. Its nth coordinate lies in the presentation kernel;
lift this coordinate through the kernel tower and subtract the resulting kernel
sequence. The difference has zero nth coordinate in the completed free module, hence
lies in I^(n+1) times that free module by the completion quotient formula (the ideal
is finitely generated because A is Noetherian). Its image is the original element,
so it lies in I^(n+1)N. Conversely I^(n+1)N maps to zero by annihilation of the nth
term. This proves the kernel equality as an A-submodule. -/
theorem adicTower_finiteLimit (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfinite : ∀ n : ℕ, Module.Finite A (T.obj (op n)))
    (hzero : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) = ⊥)
    (htrans : ∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1)))))
    (N : ModuleCat.{u} (AdicCompletion I A))
    (e : (restrictScalars (algebraMap A (AdicCompletion I A))).obj N ≅ limit T)
    (hscalar : ∀ (n : ℕ) (r : AdicCompletion I A) (a : A) (x : N),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (e.hom ≫ limit.π T (op n)) (r • x) =
        a • (e.hom ≫ limit.π T (op n)) x) :
    Module.Finite (AdicCompletion I A) N ∧
    ∀ n : ℕ, Function.Surjective (e.hom ≫ limit.π T (op n)) ∧
      LinearMap.ker (e.hom ≫ limit.π T (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((restrictScalars (algebraMap A (AdicCompletion I A))).obj N)) := by
  classical
  obtain ⟨d, q, hq⟩ := adicTower_completedFreeSurjection A I T (hfinite 0) hzero htrans N e hscalar
  have hfree : Module.Finite (AdicCompletion I A) (AdicCompletion I (Fin d → A)) :=
    Module.Finite.of_surjective (AdicCompletion.piEquivFin I d).symm.toLinearMap
      (AdicCompletion.piEquivFin I d).symm.surjective
  refine ⟨Module.Finite.of_surjective q hq, ?_⟩
  intro n
  have hp : Function.Surjective (limit.π T (op n)) := by
    let shift : ℕ ⥤ ℕ := (show Monotone (fun k : ℕ ↦ n + k) from
      fun _ _ h ↦ Nat.add_le_add_left h n).functor
    have hfinal : shift.Final := by
      apply (Monotone.final_functor_iff _).2
      intro k
      exact ⟨k, Nat.le_add_left k n⟩
    have hc := (Functor.Initial.isLimitWhiskerEquiv shift.op (limit.cone T)).symm
      (limit.isLimit T)
    have hs : ∀ k : ℕ, Function.Surjective
        ((shift.op ⋙ T).map (homOfLE (Nat.le_succ k)).op) := by
      intro k
      change Function.Surjective (T.map (homOfLE (Nat.le_succ (n + k))).op)
      exact (htrans (n + k)).1
    exact Concrete.surjective_π_app_zero_of_surjective_map hc hs
  refine ⟨hp.comp ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance), le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hq x
    obtain ⟨z, hz, heval⟩ := adicTower_freeKernelCorrection A I T hzero htrans N e
      hscalar d q hq n y hx
    have hyz : y - z ∈ I ^ (n + 1) •
        (⊤ : Submodule A (AdicCompletion I (Fin d → A))) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := Fin d → A)
        (IsNoetherian.noetherian I)]
      change AdicCompletion.eval I (Fin d → A) (n + 1) (y - z) = 0
      rw [map_sub, heval, sub_self]
    let qA : AdicCompletion I (Fin d → A) →ₗ[A]
        ((restrictScalars (algebraMap A (AdicCompletion I A))).obj N) :=
      { toFun := q
        map_add' := q.map_add
        map_smul' := fun a y ↦ by
          change q (a • y) = algebraMap A (AdicCompletion I A) a • q y
          rw [← algebraMap_smul (AdicCompletion I A) a y, q.map_smul] }
    have hm := Submodule.smul_top_le_comap_smul_top (I ^ (n + 1)) qA hyz
    simpa [qA, map_sub, hz] using hm
  · apply Submodule.smul_le.mpr
    intro a ha x _
    change (e.hom ≫ limit.π T (op n)) (a • x) = 0
    rw [map_smul]
    have hz : a • (e.hom ≫ limit.π T (op n)) x ∈
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) :=
      Submodule.smul_mem_smul ha (Submodule.mem_top)
    simpa [hzero n] using hz

end ModuleCat
