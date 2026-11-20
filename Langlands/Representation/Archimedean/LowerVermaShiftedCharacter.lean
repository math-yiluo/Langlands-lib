import Langlands.Representation.Archimedean.SphericalKernel
import Langlands.Representation.Archimedean.LowerVermaCentral
import Langlands.Representation.Archimedean.ComplexGelfandSeparation
import Mathlib.GroupTheory.Perm.Sign

/-!
# Shifted Weyl invariance of lower Verma characters

See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaShifted

open VermaGL VermaPBW VermaCentral
attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

/-- Evaluation of the lower Verma Harish-Chandra map at a diagonal weight. -/
def character (lam : Fin n → ℂ) : VermaGL.center n →ₐ[ℂ] ℂ :=
  SphericalKernel.chiV lam

theorem character_apply (lam : Fin n → ℂ) (z : VermaGL.center n) :
    character n lam z = MvPolynomial.eval lam (gam n z) := by
  simp only [character, SphericalKernel.chiV, AlgHom.comp_apply, MvPolynomial.aeval_eq_eval, gamC_apply]

/-- Every vector of lower weight `lam` has the character of the lower Verma generator. -/
theorem character_action (lam : Fin n → ℂ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : glU n →ₐ[ℂ] Module.End ℂ V) (v : V)
    (hl : ∀ p q : Fin n, q < p → A (unitU n p q) v = 0)
    (hd : ∀ p : Fin n, A (unitU n p p) v = lam p • v) (z : VermaGL.center n) :
    A z v = character n lam z • v := by
  have hmem : (z : glU n) - algebraMap ℂ (glU n) (character n lam z) ∈
      lowerVermaIdeal n lam := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub,
      mk_eq_smul_gen, mk_eq_smul_gen, VermaCentral.center_smul_gen n, algebraMap_smul,
      character_apply, sub_self]
  have hkill : ∀ u ∈ lowerVermaIdeal n lam, A u v = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      rcases hu with ⟨p, q, hpq, rfl⟩ | ⟨p, rfl⟩
      · exact hl p q hpq
      · rw [map_sub, LinearMap.sub_apply, hd, A.commutes, Module.algebraMap_end_apply,
          sub_self]
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul r x _ hx =>
      rw [smul_eq_mul, map_mul, Module.End.mul_apply, hx, map_zero]
  have h := hkill _ hmem
  rwa [map_sub, LinearMap.sub_apply, A.commutes, Module.algebraMap_end_apply, sub_eq_zero]
    at h

variable {n}

private theorem comm_action {lam : Fin n → ℂ} (a b : glU n) (v : LowerVerma n lam) :
    a • (b • v) = b • (a • v) + (a * b - b * a) • v := by
  rw [smul_smul, smul_smul, ← add_smul, add_sub_cancel]

private def stepWeight (i j p : Fin n) : ℂ :=
  (if p = i then 1 else 0) - (if p = j then 1 else 0)

private theorem diagonal_power (lam : Fin n → ℂ) (i j p : Fin n) (k : ℕ) :
    unitU n p p • (unitU n i j ^ k • gen n lam) =
      (lam p + k * stepWeight i j p) • (unitU n i j ^ k • gen n lam) := by
  induction k with
  | zero => simpa using BGChase.unitU_smul_gen_diag lam p
  | succ k ih =>
    have hcomm : unitU n p p * unitU n i j - unitU n i j * unitU n p p =
        stepWeight i j p • unitU n i j := by
      rw [unitU_comm, stepWeight, sub_smul]
      congr 1
      · split_ifs with h <;> simp [h]
      · by_cases h : p = j
        · simp [h]
        · simp [h, Ne.symm h]
    rw [pow_succ', mul_smul, comm_action, hcomm, smul_assoc, ih, smul_comm (unitU n i j),
      ← add_smul, Nat.cast_succ]
    congr 1
    ring

private theorem opposite_power (lam : Fin n → ℂ) {i j : Fin n} (hij : i < j) (k : ℕ) :
    unitU n j i • (unitU n i j ^ (k + 1) • gen n lam) =
      (((k : ℂ) + 1) * (lam j - lam i - k)) • (unitU n i j ^ k • gen n lam) := by
  have hc := unitU_comm n j i i j
  simp only [ite_true] at hc
  have hj := diagonal_power lam i j j
  have hi := diagonal_power lam i j i
  simp only [stepWeight, hij.ne, hij.ne', ite_true, ite_false, zero_sub, sub_zero,
    mul_one, mul_neg] at hj hi
  induction k with
  | zero =>
    rw [pow_succ', mul_smul, pow_zero, one_smul, comm_action, hc, sub_smul,
      BGChase.unitU_smul_gen_of_lt lam hij, smul_zero, zero_add,
      BGChase.unitU_smul_gen_diag, BGChase.unitU_smul_gen_diag, ← sub_smul]
    simp
  | succ k ih =>
    rw [pow_succ', mul_smul, comm_action, hc, ih, smul_comm (unitU n i j),
      ← mul_smul, ← pow_succ', sub_smul, hj, hi, ← sub_smul, ← add_smul]
    congr 1
    push_cast
    ring

private theorem lower_power_of_ne (lam : Fin n → ℂ) {i j : Fin n} (hij : i < j)
    (hadj : j.val = i.val + 1) {p q : Fin n} (hqp : q < p)
    (hne : (p, q) ≠ (j, i)) (k : ℕ) :
    unitU n p q • (unitU n i j ^ k • gen n lam) = 0 := by
  have kill_of_comm {a b : Fin n} (hab : b < a) (hq : b ≠ i) (hp : a ≠ j) (m : ℕ) :
      unitU n a b • (unitU n i j ^ m • gen n lam) = 0 := by
    induction m with
    | zero => simpa using BGChase.unitU_smul_gen_of_lt lam hab
    | succ m ih =>
      rw [pow_succ', mul_smul, comm_action, unitU_comm, ite_eq_right hq, ite_eq_right hp.symm,
        sub_self, zero_smul, ih, smul_zero, add_zero]
  induction k with
  | zero => simpa using BGChase.unitU_smul_gen_of_lt lam hqp
  | succ k ih =>
    rw [pow_succ', mul_smul, comm_action, unitU_comm, ih, smul_zero, zero_add]
    by_cases hq : q = i
    · subst q
      have hp : p ≠ j := fun h => hne (by rw [h])
      have hlt : j < p := by
        have hval : p.val ≠ j.val := fun h => hp (Fin.ext h)
        have horder := Fin.lt_def.mp hqp
        exact Fin.lt_def.mpr (by omega)
      rw [ite_eq_left rfl, ite_eq_right hp.symm, sub_zero, kill_of_comm hlt hij.ne' hp]
    · rw [ite_eq_right hq]
      by_cases hp : j = p
      · subst p
        have hlt : q < i := by
          have hval : q.val ≠ i.val := fun h => hq (Fin.ext h)
          have horder := Fin.lt_def.mp hqp
          exact Fin.lt_def.mpr (by omega)
        rw [ite_eq_left rfl, sub_smul, zero_smul, kill_of_comm hlt hq hij.ne, sub_zero]
      · rw [ite_eq_right hp, sub_self, zero_smul]

private theorem upper_power_ne_zero (lam : Fin n → ℂ) {i j : Fin n} (hij : i < j)
    (hadj : j.val = i.val + 1) (k : ℕ) : unitU n i j ^ k • gen n lam ≠ 0 := by
  have heval : ∀ m : ℕ, Psi n (vVal n lam 1) (unitU n i j ^ m) = 1 := by
    intro m
    induction m with
    | zero => rw [pow_zero, Psi_one]
    | succ m ih =>
      rw [pow_succ']
      change Psi n (vVal n lam 1)
          (UniversalEnvelopingAlgebra.ι ℂ (unitE n (i, j)) * unitU n i j ^ m) = 1
      rw [Psi_unitE_up_mul n lam 1 ⟨(i, j), hij⟩, ih]
      simp [vVal, supCoeff, hij, hadj]
  intro hz
  rw [← mk_eq_smul_gen, Submodule.Quotient.mk_eq_zero] at hz
  have h := Psi_mul_mem_lowerVermaIdeal n lam 1 hz 1
  rw [one_mul, heval] at h
  exact one_ne_zero h

/-- Permute the shifted coordinates `lam i + i` and then remove the shift. -/
def shift (σ : Equiv.Perm (Fin n)) (lam : Fin n → ℂ) (p : Fin n) : ℂ :=
  lam (σ p) + (σ p).val - p.val

private theorem character_swap_of_sub_eq_nat (lam : Fin n → ℂ) {i j : Fin n}
    (hij : i < j) (hadj : j.val = i.val + 1) (k : ℕ) (hk : lam j - lam i = k)
    (z : VermaGL.center n) :
    character n (shift (Equiv.swap i j) lam) z = character n lam z := by
  let v := unitU n i j ^ (k + 1) • gen n lam
  have hcast : (j.val : ℂ) = (i.val : ℂ) + 1 := by rw [hadj, Nat.cast_add, Nat.cast_one]
  have hwt (p : Fin n) : lam p + ((k + 1 : ℕ) : ℂ) * stepWeight i j p =
      shift (Equiv.swap i j) lam p := by
    by_cases hpi : p = i
    · subst p
      simp only [shift, Equiv.swap_apply_left, stepWeight, ite_true, hij.ne, ite_false,
        sub_zero, mul_one, Nat.cast_add, Nat.cast_one, hcast]
      linear_combination -hk
    · by_cases hpj : p = j
      · subst p
        simp only [shift, Equiv.swap_apply_right, stepWeight, ite_true, hij.ne', ite_false,
          zero_sub, mul_neg, mul_one, Nat.cast_add, Nat.cast_one, hcast]
        linear_combination hk
      · simp [shift, stepWeight, Equiv.swap_apply_of_ne_of_ne hpi hpj, hpi, hpj]
  have hl (p q : Fin n) (hqp : q < p) : unitU n p q • v = 0 := by
    by_cases hpq : (p, q) = (j, i)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpq
      unfold v
      rw [opposite_power lam hij, hk, sub_self, mul_zero, zero_smul]
    · exact lower_power_of_ne lam hij hadj hqp hpq (k + 1)
  have hd (p : Fin n) : unitU n p p • v = shift (Equiv.swap i j) lam p • v := by
    unfold v
    rw [diagonal_power, hwt]
  have h := character_action n (shift (Equiv.swap i j) lam)
    (Algebra.lsmul ℂ ℂ (LowerVerma n lam)) v hl hd z
  change (z : glU n) • v = character n (shift (Equiv.swap i j) lam) z • v at h
  have hz : unitU n i j ^ (k + 1) * (z : glU n) = (z : glU n) * unitU n i j ^ (k + 1) :=
    Subalgebra.mem_center_iff.mp z.2 _
  have hscalar : (z : glU n) • v = character n lam z • v := by
    unfold v
    rw [smul_smul, ← hz, mul_smul, VermaCentral.center_smul_gen, ← character_apply, smul_comm]
  exact smul_left_injective ℂ (upper_power_ne_zero lam hij hadj (k + 1)) (h.symm.trans hscalar)

private theorem character_swap (lam : Fin n → ℂ) {i j : Fin n} (hij : i < j)
    (hadj : j.val = i.val + 1) : character n (shift (Equiv.swap i j) lam) = character n lam := by
  ext z
  let σ := Equiv.swap i j
  let f (r : Fin n) : Polynomial ℂ := if r = j then Polynomial.X else Polynomial.C (lam r)
  let g (r : Fin n) : Polynomial ℂ := f (σ r) + Polynomial.C ((σ r).val - (r.val : ℂ))
  let w (t : ℂ) (r : Fin n) : ℂ := if r = j then t else lam r
  let P := MvPolynomial.aeval f (gamC n z)
  let Q := MvPolynomial.aeval g (gamC n z)
  have hP (t : ℂ) : Polynomial.eval t P = character n (w t) z := by
    change Polynomial.aeval t (MvPolynomial.aeval f (gamC n z)) =
      MvPolynomial.aeval (w t) (gamC n z)
    rw [MvPolynomial.comp_aeval_apply]
    congr 2
    funext r
    by_cases hr : r = j <;> simp [f, w, hr]
  have hQ (t : ℂ) : Polynomial.eval t Q = character n (shift σ (w t)) z := by
    change Polynomial.aeval t (MvPolynomial.aeval g (gamC n z)) =
      MvPolynomial.aeval (shift σ (w t)) (gamC n z)
    rw [MvPolynomial.comp_aeval_apply]
    congr 2
    funext r
    by_cases hr : σ r = j <;> simp [g, f, w, shift, hr, sub_eq_add_neg, add_assoc]
  have hrange : Set.Infinite (Set.range fun k : ℕ => lam i + (k : ℂ)) :=
    Set.infinite_range_of_injective (fun _ _ h => Nat.cast_injective (add_left_cancel h))
  have hQP : Q = P := Polynomial.eq_of_infinite_eval_eq Q P (hrange.mono (by
    rintro _ ⟨k, rfl⟩
    rw [Set.mem_ofPred_eq, hQ, hP]
    apply character_swap_of_sub_eq_nat _ hij hadj k
    simp [w, hij.ne]))
  have hw : w (lam j) = lam := by
    funext r
    by_cases hr : r = j <;> simp [w, hr]
  rw [← hw, ← hQ, hQP, hP]

/-- The full center character is invariant under shifted permutations. -/
theorem character_shift (σ : Equiv.Perm (Fin n)) (lam : Fin n → ℂ) :
    character n (shift σ lam) = character n lam := by
  cases n with
  | zero =>
    have h : shift σ lam = lam := funext fun i => i.elim0
    rw [h]
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n + 1))) :=
      { carrier := {σ | ∀ w, character (n + 1) (shift σ w) = character (n + 1) w}
        one_mem' := by
          change ∀ w, character (n + 1) (shift 1 w) = character (n + 1) w
          intro w
          have h : shift 1 w = w := by funext r; simp [shift]
          rw [h]
        mul_mem' := by
          intro a b ha hb w
          have h : shift (a * b) w = shift b (shift a w) := by
            funext r
            simp only [shift, Equiv.Perm.mul_apply]
            ring
          rw [h, hb, ha] }
    have hS : Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ S :=
      Submonoid.closure_le.mpr (by
        rintro _ ⟨i, rfl⟩ w
        exact character_swap w Fin.castSucc_lt_succ rfl)
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hS
    exact hS (Submonoid.mem_top σ) lam

/-- Two lower Verma characters agree exactly when their shifted coordinates are permuted. -/
theorem character_eq_iff (lam mu : Fin n → ℂ) :
    character n lam = character n mu ↔
      ∃ σ : Equiv.Perm (Fin n), ∀ p, lam p + (p.val : ℂ) = mu (σ p) + ((σ p).val : ℂ) := by
  constructor
  · intro h
    apply GelfandSeparation.exists_perm_of_gel_eq
    intro k
    have hz := DFunLike.congr_fun h (⟨gel n k, gel_mem_center n k⟩ : VermaGL.center n)
    simpa only [character_apply, gam_gel, map_sum, GelfandSeparation.gv] using hz
  · rintro ⟨σ, hσ⟩
    have h : lam = shift σ mu := by
      funext p
      exact eq_sub_of_add_eq (hσ p)
    rw [h, character_shift]

end Langlands.Archimedean.VermaShifted
