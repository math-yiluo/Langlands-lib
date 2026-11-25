/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.CategoryTheory.Filtered.Final

/-! # Completed free presentations for adic towers

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/-- The scalar residue equation makes a projected presentation vanish on the free
evaluation kernel, by expansion in the finite completed basis. -/
private theorem free_residue_zero (A : Type u) [CommRing A] (I : Ideal A)
    (N : ModuleCat.{u} (AdicCompletion I A)) (M : ModuleCat.{u} A)
    (L : (restrictScalars (algebraMap A (AdicCompletion I A))).obj N ⟶ M)
    (k : ℕ)
    (hscalar : ∀ (r : AdicCompletion I A) (a : A) (x : N),
      AdicCompletion.evalₐ I k r = Ideal.Quotient.mk (I ^ k) a →
      L (r • x) = a • L x)
    (d : ℕ) (q : AdicCompletion I (Fin d → A) →ₗ[AdicCompletion I A] N)
    (y : AdicCompletion I (Fin d → A))
    (hy : AdicCompletion.eval I (Fin d → A) k y = 0) : L (q y) = 0 := by
  classical
  let b := Module.Basis.ofEquivFun (AdicCompletion.piEquivFin I d)
  have hc (i : Fin d) : AdicCompletion.evalₐ I k (b.repr y i) = 0 := by
    rw [Module.Basis.ofEquivFun_repr_apply]
    have hv : (AdicCompletion.piEquivFin I d y i).val k = 0 := by
      simp only [AdicCompletion.piEquivFin_apply, AdicCompletion.pi,
        LinearMap.pi_apply, AdicCompletion.map_val_apply]
      change (LinearMap.proj i).reduceModIdeal (I ^ k)
        (AdicCompletion.eval I (Fin d → A) k y) = 0
      rw [hy, map_zero]
    rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
    rw [show AdicCompletion.eval I A k (AdicCompletion.piEquivFin I d y i) = 0
      from hv, map_zero]
  rw [← b.sum_repr y, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [q.map_smul]
  simpa using hscalar (b.repr y i) 0 (q (b i)) (by simpa using hc i)

/-- Compatible stabilized residues define a vector of the completion, even when
the ideal is not finitely generated. -/
private theorem completion_stabilize (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ)
    (f : ℕ → AdicCompletion I M)
    (hf : ∀ k : ℕ, AdicCompletion.eval I M (n + k + 1) (f (k + 1)) =
      AdicCompletion.eval I M (n + k + 1) (f k)) :
    ∃ z : AdicCompletion I M, ∀ k : ℕ,
      AdicCompletion.eval I M (n + k + 1) z =
        AdicCompletion.eval I M (n + k + 1) (f k) := by
  have hlow (m k : ℕ) (hm : m ≤ n + k + 1) :
      AdicCompletion.eval I M m (f (k + 1)) = AdicCompletion.eval I M m (f k) := by
    have h := congrArg (AdicCompletion.transitionMap I M hm) (hf k)
    simpa only [AdicCompletion.eval_apply,
      AdicCompletion.transitionMap_comp_eval_apply] using h
  have hstable (m k l : ℕ) (hm : m ≤ n + k + 1) (hkl : k ≤ l) :
      AdicCompletion.eval I M m (f l) = AdicCompletion.eval I M m (f k) := by
    induction l, hkl using Nat.le_induction with
    | base => rfl
    | succ l hkl ih =>
      exact (hlow m l (by omega)).trans ih
  let z : AdicCompletion I M :=
    ⟨fun m ↦ AdicCompletion.eval I M m (f m), by
      intro m l hml
      change AdicCompletion.transitionMap I M hml ((f l).val l) = (f m).val m
      rw [AdicCompletion.transitionMap_comp_eval_apply]
      exact hstable m m l (by omega) hml⟩
  refine ⟨z, fun k ↦ ?_⟩
  change AdicCompletion.eval I M (n + k + 1) (f (n + k + 1)) = _
  exact hstable (n + k + 1) k (n + k + 1) (by omega) (by omega)

/-- A vector mapping to zero at one tower level can be corrected by a global
presentation-kernel vector with the same free residue at that level.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof, the surjection
K → K_n used in the final cokernel calculation.
(blueprint: lem-weil-pbc-adic-tower-free-kernel-correction).

Proof: Put P = A^d and P_n = P/I^(n+1)P. The map q followed by the nth
projection factors through P_n: identify the completed free module with a
finite product of the completed ring, choose representatives of each residue,
and use the completed scalar equation on each basis vector. Hence the projected
value depends only on the residue, and the factor is A-linear. The
tower projections are surjective by recursive lifting along htrans. Hence
q surjective makes each composite to T_n surjective, and its factor
P_n → T_n is surjective. The factors commute with transitions, as equality
can be tested on lifts to the completed free module. Let K_n be their kernels.
Lift a K_n vector to P_(n+1). Its image in T_(n+1) lies in I^(n+1)T_(n+1).
Surjectivity of P_(n+1) → T_(n+1) supplies an I^(n+1) correction vector;
subtracting it proves that K_(n+1) → K_n is surjective. Thus every K_n vector
lifts to a compatible kernel sequence. The identification of the free
completion with lim P_n makes that sequence a vector z. Every coordinate
of q(z) is zero, so limit extensionality and injectivity of e give q(z)=0.
Apply this to the residue of y, which lies in K_n by the given equation.
The resulting z has the same nth residue as y. No finite generation of T_n
or Noetherian hypothesis is used in this correction argument. -/
theorem adicTower_freeKernelCorrection (A : Type u) [CommRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
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
        a • (e.hom ≫ limit.π T (op n)) x)
    (d : ℕ) (q : AdicCompletion I (Fin d → A) →ₗ[AdicCompletion I A] N)
    (hq : Function.Surjective q) (n : ℕ) (y : AdicCompletion I (Fin d → A))
    (hy : (e.hom ≫ limit.π T (op n)) (q y) = 0) :
    ∃ z : AdicCompletion I (Fin d → A), q z = 0 ∧
      AdicCompletion.eval I (Fin d → A) (n + 1) z =
        AdicCompletion.eval I (Fin d → A) (n + 1) y := by
  classical
  have _hzero := hzero
  let P := AdicCompletion I (Fin d → A)
  let qA : P →ₗ[A]
      ((restrictScalars (algebraMap A (AdicCompletion I A))).obj N) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun a x ↦ by
        change q (a • x) = algebraMap A (AdicCompletion I A) a • q x
        rw [← algebraMap_smul (AdicCompletion I A) a x, q.map_smul] }
  let p (j : ℕ) : P →ₗ[A] T.obj (op j) :=
    (e.hom ≫ limit.π T (op j)).hom.comp qA
  have hp (j : ℕ) : Function.Surjective (p j) := by
    have hπ : Function.Surjective (limit.π T (op j)) := by
      let shift : ℕ ⥤ ℕ := (show Monotone (fun k : ℕ ↦ j + k) from
        fun _ _ h ↦ Nat.add_le_add_left h j).functor
      have hfinal : shift.Final := by
        apply (Monotone.final_functor_iff _).2
        intro k
        exact ⟨k, Nat.le_add_left k j⟩
      have hc := (Functor.Initial.isLimitWhiskerEquiv shift.op (limit.cone T)).symm
        (limit.isLimit T)
      have hs : ∀ k : ℕ, Function.Surjective
          ((shift.op ⋙ T).map (homOfLE (Nat.le_succ k)).op) := by
        intro k
        exact (htrans (j + k)).1
      exact Concrete.surjective_π_app_zero_of_surjective_map hc hs
    exact hπ.comp (((ModuleCat.epi_iff_surjective e.hom).mp inferInstance).comp hq)
  have hcompat (j : ℕ) (x : P) :
      T.map (homOfLE (Nat.le_succ j)).op (p (j + 1) x) = p j x := by
    change ((e.hom ≫ limit.π T (op (j + 1))) ≫
      T.map (homOfLE (Nat.le_succ j)).op) (q x) =
        (e.hom ≫ limit.π T (op j)) (q x)
    rw [Category.assoc, limit.w]
  have hstep (j : ℕ) (x : P) (hx : p j x = 0) :
      ∃ x' : P, p (j + 1) x' = 0 ∧
        AdicCompletion.eval I (Fin d → A) (j + 1) x' =
          AdicCompletion.eval I (Fin d → A) (j + 1) x := by
    have hm : p (j + 1) x ∈ I ^ (j + 1) •
        (⊤ : Submodule A (T.obj (op (j + 1)))) := by
      rw [← (htrans j).2]
      exact (hcompat j x).trans hx
    have hmap : (I ^ (j + 1) • (⊤ : Submodule A P)).map (p (j + 1)) =
        I ^ (j + 1) • (⊤ : Submodule A (T.obj (op (j + 1)))) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hp _)]
    rw [← hmap] at hm
    obtain ⟨w, hw, heq⟩ := Submodule.mem_map.mp hm
    refine ⟨x - w, ?_, ?_⟩
    · rw [map_sub, heq, sub_self]
    · have hw0 := AdicCompletion.pow_smul_top_le_ker_eval (M := Fin d → A) I (j + 1) hw
      change AdicCompletion.eval I (Fin d → A) (j + 1) w = 0 at hw0
      rw [map_sub, hw0, sub_zero]
  let next (k : ℕ) (x : {x : P // p (n + k) x = 0}) :
      {x : P // p (n + (k + 1)) x = 0} :=
    ⟨(hstep (n + k) x x.property).choose, (hstep (n + k) x x.property).choose_spec.1⟩
  let f' : ∀ k : ℕ, {x : P // p (n + k) x = 0} :=
    Nat.rec (⟨y, hy⟩ : {x : P // p (n + 0) x = 0}) next
  let f (k : ℕ) : P := (f' k).val
  have hf (k : ℕ) : AdicCompletion.eval I (Fin d → A) (n + k + 1) (f (k + 1)) =
      AdicCompletion.eval I (Fin d → A) (n + k + 1) (f k) := by
    dsimp only [f, f', Nat.rec, next]
    exact (hstep (n + k) (f' k).val (f' k).property).choose_spec.2
  obtain ⟨z, hz⟩ := completion_stabilize A I (Fin d → A) n f hf
  have hpz (k : ℕ) : p (n + k) z = 0 := by
    have hres : AdicCompletion.eval I (Fin d → A) (n + k + 1) (z - f k) = 0 := by
      rw [map_sub, hz k, sub_self]
    have h := free_residue_zero A I N (T.obj (op (n + k)))
      (e.hom ≫ limit.π T (op (n + k))) (n + k + 1) (hscalar (n + k)) d q
      (z - f k) hres
    change p (n + k) (z - f k) = 0 at h
    rw [map_sub, (f' k).property, sub_zero] at h
    exact h
  have hzq : q z = 0 := by
    have he : e.hom (q z) = e.hom 0 := by
      apply Concrete.limit_ext T
      intro j
      have h := hpz j.unop
      have hπ := limit.w T (homOfLE (show j.unop ≤ n + j.unop from
        Nat.le_add_left _ _)).op
      have heq := congrArg (fun g ↦ (e.hom ≫ g) (q z)) hπ
      change T.map (homOfLE _).op (p (n + j.unop) z) = p j.unop z at heq
      rw [h, map_zero] at heq
      simpa [p, qA] using heq.symm
    exact ((ModuleCat.mono_iff_injective e.hom).mp inferInstance) he
  refine ⟨z, hzq, ?_⟩
  have h0 : f 0 = y := rfl
  simpa only [Nat.add_zero, h0] using hz 0

end ModuleCat
