import Langlands.LinearAlgebra.SimplyConnectedRootDatum
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Fixed vectors of an ordered product of simple reflections -/

noncomputable section

open scoped BigOperators

namespace Langlands.LinearAlgebra

section Linear

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem sum_path_differences (r : ℕ) (v : Fin (r + 1) → M) :
    ∑ j : Fin r, (v j.castSucc - v j.succ) = v 0 - v (Fin.last r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun j => v j.succ)
    simp only [Fin.succ_castSucc] at ht
    rw [ht]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    abel

private theorem closed_path_coefficients {r : ℕ} (a : Fin r → M)
    (ha : LinearIndependent R a) (v : Fin (r + 1) → M) (c : Fin r → R)
    (hstep : ∀ j, v j.castSucc - v j.succ = c j • a j)
    (hclose : v 0 = v (Fin.last r)) : ∀ j, c j = 0 := by
  apply Fintype.linearIndependent_iff.mp ha
  simp_rw [← hstep]
  rw [sum_path_differences, hclose, sub_self]

omit [AddCommGroup M] in
private theorem path_constant {r : ℕ} (v : Fin (r + 1) → M)
    (hstep : ∀ j : Fin r, v j.castSucc = v j.succ) : ∀ j, v j = v 0 := by
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih => exact (hstep j).symm.trans ih

/-- Successive suffix images of a finite ordered family of linear automorphisms. -/
def orderedLinearOrbit : (r : ℕ) → (Fin r → M ≃ₗ[R] M) → M → Fin (r + 1) → M
  | 0, _, x => fun _ => x
  | r + 1, f, x => Fin.cons ((List.ofFn f).prod x)
      (orderedLinearOrbit r (fun j => f j.succ) x)

private theorem orderedLinearOrbit_zero (r : ℕ) (f : Fin r → M ≃ₗ[R] M) (x : M) :
    orderedLinearOrbit r f x 0 = (List.ofFn f).prod x := by
  cases r with
  | zero => simp [orderedLinearOrbit]
  | succ r => rfl

private theorem orderedLinearOrbit_last (r : ℕ) (f : Fin r → M ≃ₗ[R] M) (x : M) :
    orderedLinearOrbit r f x (Fin.last r) = x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simpa only [orderedLinearOrbit, ← Fin.succ_last, Fin.cons_succ] using
      ih (fun j => f j.succ)

private theorem orderedLinearOrbit_step (r : ℕ) (f : Fin r → M ≃ₗ[R] M) (x : M)
    (j : Fin r) :
    orderedLinearOrbit r f x j.castSucc =
      f j (orderedLinearOrbit r f x j.succ) := by
  induction r with
  | zero => exact j.elim0
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.castSucc_zero, orderedLinearOrbit, Fin.cons_zero, Fin.cons_succ,
        orderedLinearOrbit_zero, List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]
    · simpa only [← Fin.succ_castSucc, orderedLinearOrbit, Fin.cons_succ] using
        ih (fun i => f i.succ) j

/-- For independent reflection directions, an ordered product fixes a vector
exactly when every specified reflecting linear form annihilates that vector. -/
theorem orderedReflection_fixed_iff {r : ℕ} (a : Fin r → M)
    (ha : LinearIndependent R a) (l : Fin r → M →ₗ[R] R)
    (f : Fin r → M ≃ₗ[R] M)
    (hf : ∀ j y, f j y = y - l j y • a j) (x : M) :
    (List.ofFn f).prod x = x ↔ ∀ j, l j x = 0 := by
  constructor
  · intro hx
    let v := orderedLinearOrbit r f x
    have hstep (j : Fin r) : v j.castSucc - v j.succ =
        (-l j (v j.succ)) • a j := by
      dsimp only [v]
      rw [orderedLinearOrbit_step, hf]
      module
    have hclose : v 0 = v (Fin.last r) := by
      dsimp only [v]
      rw [orderedLinearOrbit_zero, orderedLinearOrbit_last, hx]
    have hc := closed_path_coefficients a ha v _ hstep hclose
    have hconstant : ∀ j, v j = v 0 := path_constant v fun j => by
      apply sub_eq_zero.mp
      rw [hstep, hc, zero_smul]
    intro j
    have hv : v j.succ = x := by
      rw [hconstant]
      dsimp only [v]
      rw [orderedLinearOrbit_zero, hx]
    have h := hc j
    rw [hv, neg_eq_zero] at h
    exact h
  · intro hl
    have hfix (j : Fin r) : f j x = x := by rw [hf, hl, zero_smul, sub_zero]
    clear hf ha hl
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply,
        ih (fun j => a j.succ) (fun j => l j.succ) (fun j => f j.succ)
          (fun j => hfix j.succ), hfix]

end Linear

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    (b : P.Base) {r : ℕ} (e : Fin r ≃ b.support)

/-- The product of all simple reflections in the supplied order. -/
def orderedCoxeter : M ≃ₗ[R] M :=
  (List.ofFn fun j => P.reflection (e j)).prod

/-- The fixed space of an ordered Coxeter product is the common annihilator
of the simple coroots; central directions are retained for reductive data. -/
theorem orderedCoxeter_eq_self_iff (x : M) :
    orderedCoxeter b e x = x ↔ ∀ a : b.support, P.coroot' a x = 0 := by
  rw [orderedCoxeter, orderedReflection_fixed_iff
    (fun j => P.root (e j)) (b.linearIndepOn_root.comp e e.injective)
    (fun j => P.coroot' (e j)) (fun j => P.reflection (e j))
    (fun j y => P.reflection_apply (e j) y)]
  constructor
  · intro h a
    simpa using h (e.symm a)
  · intro h j
    exact h (e j)

end RootPairing

section RootDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite ι]
    {P : RootDatum ι X Y} (b : P.Base) {r : ℕ} (e : Fin r ≃ b.support)

/-- Finite coroot index removes every central fixed direction of a Coxeter product. -/
theorem orderedCoxeter_eq_self_iff_eq_zero
    (hfin : Finite (Y ⧸ P.corootSpan ℤ)) (x : X) :
    orderedCoxeter b e x = x ↔ x = 0 := by
  rw [orderedCoxeter_eq_self_iff]
  constructor
  · intro hx
    have hker : P.corootSpan ℤ ≤ LinearMap.ker (P.toLinearMap x) := by
      rw [← b.span_coroot_support]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact hx ⟨a, ha⟩
    apply SimplyConnectedRootDatum.injective_toRootDatum_weightMap P hfin
    rw [map_zero]
    ext y
    exact hker y.property
  · rintro rfl a
    exact map_zero _

end RootDatum

end Langlands.LinearAlgebra
