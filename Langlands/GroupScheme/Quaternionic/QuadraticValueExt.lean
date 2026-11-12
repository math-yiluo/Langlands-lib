import Langlands.GroupScheme.Quaternionic.HyperbolicPair
import Langlands.GroupScheme.Quaternionic.QuadraticPullback
import Mathlib.Data.Fintype.EquivFin

/-! # Detecting quaternionic quadratic forms by their vector values -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open scoped Matrix

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- The alternating subspace of a unital involution is proper. -/
theorem alternatingSubspace_ne_top : σ.alternatingSubspace ≠ ⊤ := by
  intro ht
  have hall (z : D) : z ∈ σ.alternatingSubspace := by rw [ht]; trivial
  have hneg (z : D) : σ z = -z := by
    obtain ⟨a, ha⟩ := σ.mem_alternatingSubspace.mp (hall z)
    rw [← ha, map_sub, apply_apply, neg_sub]
  have htwo : (1 : D) + 1 = 0 := by
    exact eq_neg_iff_add_eq_zero.mp (by simpa only [map_one] using hneg 1)
  obtain ⟨a, ha⟩ := σ.mem_alternatingSubspace.mp (hall 1)
  have h10 : (1 : D) = 0 := by
    calc
      1 = a - σ a := ha.symm
      _ = a + a := by rw [hneg, sub_neg_eq_add]
      _ = (1 + 1) * a := by rw [add_mul, one_mul]
      _ = 0 := by rw [htwo, zero_mul]
  exact one_ne_zero h10

/-- No nonzero left multiple of the whole division algebra lies in the alternating subspace. -/
theorem eq_zero_of_forall_mul_mem_alternatingSubspace (c : D)
    (hc : ∀ a : D, c * a ∈ σ.alternatingSubspace) : c = 0 := by
  by_contra hc0
  apply σ.alternatingSubspace_ne_top
  apply top_unique
  intro z _
  simpa only [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] using hc (c⁻¹ * z)

/-- A matrix is an alternating difference exactly when it is skew-hermitian and
its diagonal entries are alternating. -/
theorem mem_quadraticKernel_iff (Q : Matrix n n D) :
    Q ∈ σ.quadraticKernel n ↔
      σ.matrix n Q = -Q ∧ ∀ i, Q i i ∈ σ.alternatingSubspace := by
  constructor
  · intro h
    obtain ⟨W, hW⟩ := (σ.matrix n).mem_alternatingSubspace.mp h
    constructor
    · rw [← hW, map_sub, apply_apply]
      abel
    · intro i
      rw [← hW]
      exact σ.sub_mem_alternatingSubspace (W i i)
  · rintro ⟨hskew, hdiag⟩
    choose a ha using fun i => σ.mem_alternatingSubspace.mp (hdiag i)
    let e := Fintype.equivFin n
    let W : Matrix n n D := fun i j => if e i < e j then Q i j else if i = j then a i else 0
    apply (σ.matrix n).mem_alternatingSubspace.mpr
    refine ⟨W, ?_⟩
    ext i j
    change W i j - σ (W j i) = Q i j
    by_cases hij : i = j
    · subst j
      simpa only [W, lt_self_iff_false, ↓reduceIte] using ha i
    · have he : e i ≠ e j := fun h => hij (e.injective h)
      by_cases hlt : e i < e j
      · have hgt : ¬e j < e i := not_lt_of_ge hlt.le
        simp only [W, hlt, hgt, Ne.symm hij, ↓reduceIte, map_zero, sub_zero]
      · have hgt : e j < e i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
        have hji : σ (Q j i) = -Q i j := congrFun (congrFun hskew i) j
        simp only [W, hlt, hgt, hij, ↓reduceIte, zero_sub, hji, neg_neg]

/-- If all values vanish, all entries of the polar matrix vanish. -/
theorem polar_eq_zero_of_forall_quadraticValue_eq_zero (q : σ.QuadraticForms n)
    (hq : ∀ z : n → D, σ.quadraticValue z q = 0) : σ.polar q = 0 := by
  have hp (z z' : n → D) :
      (Submodule.Quotient.mk (σ.sesqForm (σ.polar q) z z') :
        D ⧸ σ.alternatingSubspace) = 0 := by
    have hh := σ.quadraticValue_add z z' q
    rw [hq, hq, hq, zero_add, zero_add] at hh
    exact hh.symm
  ext i j
  apply σ.eq_zero_of_forall_mul_mem_alternatingSubspace
  intro a
  have hh := (Submodule.Quotient.mk_eq_zero σ.alternatingSubspace).mp
    (hp (Pi.single i 1) (Pi.single j (σ a)))
  simpa only [sesqForm_single_right, Matrix.single_vecMul, one_smul,
    Matrix.row_apply, apply_apply] using hh

/-- A quotient-valued quadratic form is zero when it vanishes on every vector. -/
theorem eq_zero_of_forall_quadraticValue_eq_zero (q : σ.QuadraticForms n)
    (hq : ∀ z : n → D, σ.quadraticValue z q = 0) : q = 0 := by
  have hp := σ.polar_eq_zero_of_forall_quadraticValue_eq_zero q hq
  induction q using Submodule.Quotient.induction_on with
  | _ Q =>
    rw [Submodule.Quotient.mk_eq_zero]
    apply (σ.mem_quadraticKernel_iff Q).mpr
    constructor
    · rw [polar_mk] at hp
      calc
        σ.matrix n Q = (Q + σ.matrix n Q) - Q := by abel
        _ = -Q := by rw [hp, zero_sub]
    · intro i
      have hh := (Submodule.Quotient.mk_eq_zero σ.alternatingSubspace).mp (hq (Pi.single i 1))
      simpa only [quadraticValue_mk, evalLinear_apply, sesqForm_single_right, Matrix.single_vecMul,
        one_smul, Matrix.row_apply, map_one, mul_one] using hh

/-- The vector values determine the quadratic form in the published matrix quotient. -/
theorem quadraticValue_ext {q q' : σ.QuadraticForms n}
    (h : ∀ z : n → D, σ.quadraticValue z q = σ.quadraticValue z q') : q = q' := by
  apply sub_eq_zero.mp
  apply σ.eq_zero_of_forall_quadraticValue_eq_zero
  intro z
  rw [LinearMap.map_sub, h z, sub_self]

/-- Matrix congruence evaluates by applying the matrix to both row arguments. -/
theorem sesqForm_congruence (U Q : Matrix n n D) (z z' : n → D) :
    σ.sesqForm (U * Q * σ.matrix n U) z z' =
      σ.sesqForm Q (z ᵥ* U) (z' ᵥ* U) :=
  (σ.sesqForm_vecMul Q U z z').symm

/-- Pullback has the expected values on every vector. -/
theorem quadraticValue_pullback (U : Matrix n n D) (q : σ.QuadraticForms n) (z : n → D) :
    σ.quadraticValue z (σ.quadraticPullback U q) = σ.quadraticValue (z ᵥ* U) q :=
  σ.quadraticValue_quadraticPullback U q z

/-- The actual congruence condition is equivalent to preserving all vector values. -/
theorem quadraticPullback_eq_iff (U : Matrix n n D) (q : σ.QuadraticForms n) :
    σ.quadraticPullback U q = q ↔
      ∀ z : n → D, σ.quadraticValue (z ᵥ* U) q = σ.quadraticValue z q := by
  constructor
  · intro h z
    rw [← quadraticValue_pullback, h]
  · intro h
    apply σ.quadraticValue_ext
    intro z
    rw [quadraticValue_pullback, h]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
