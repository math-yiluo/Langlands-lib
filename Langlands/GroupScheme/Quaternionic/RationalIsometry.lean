import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Langlands.GroupScheme.Quaternionic.QuadraticFormIdentities
import Mathlib.Tactic.NoncommRing

/-!
# Rational isometries of a quadratic form over an algebra with involution

For an involution of the first kind `σ` of a division algebra `D` over a field `K` and a
`σ`-quadratic form `q` on row vectors `D^n` in the sense of Tits, this module studies the
units `u` of `M_n(D)` with `u Q ᵗu^σ - Q ∈ {x - ᵗx^σ}` for a representative `Q` of `q`: the
rational points of the isometry group `O(q)`. A unit acts on row vectors by `v ↦ v u`.

The main result is a criterion: when `n` is linearly ordered, `u` is such an isometry exactly
when it preserves the polar form `h(x, y)` and the values `q(x)`.
-/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution.Eichler

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n]

/-! ### The alternating subspace -/

section Alternating

variable {A : Type*} [Ring A] [Algebra K A] (τ : FirstKindInvolution K A)

/-- An involution of the first kind is the identity modulo the alternating subspace. -/
theorem sub_map_mem_alternatingSubspace (a : A) : τ a - a ∈ τ.alternatingSubspace := by
  have h := τ.sub_mem_alternatingSubspace (τ a)
  rwa [apply_apply] at h

/-- The alternating subspace is stable under `z ↦ d z τ(d)`. -/
theorem mul_mul_map_mem_alternatingSubspace {z : A} (hz : z ∈ τ.alternatingSubspace)
    (d : A) : d * z * τ d ∈ τ.alternatingSubspace := by
  obtain ⟨a, rfl⟩ := τ.mem_alternatingSubspace.1 hz
  refine τ.mem_alternatingSubspace.2 ⟨d * a * τ d, ?_⟩
  simp only [map_mul, apply_apply]
  noncomm_ring

/-- An alternating element is antisymmetric. -/
theorem map_eq_neg_of_mem_alternatingSubspace {z : A} (hz : z ∈ τ.alternatingSubspace) :
    τ z = -z := by
  obtain ⟨a, rfl⟩ := τ.mem_alternatingSubspace.1 hz
  simp

/-- The sum `z + τ z` of an alternating element vanishes. -/
theorem add_map_eq_zero_of_mem_alternatingSubspace {z : A}
    (hz : z ∈ τ.alternatingSubspace) : z + τ z = 0 := by
  rw [map_eq_neg_of_mem_alternatingSubspace τ hz, add_neg_cancel]

end Alternating

/-! ### Sesquilinear forms -/

variable [DecidableEq n]

omit [DecidableEq n] in
@[simp] theorem sesqForm_neg_left (H : Matrix n n D) (x y : n → D) :
    σ.sesqForm H (-x) y = -σ.sesqForm H x y := by
  simp only [sesqForm, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

omit [DecidableEq n] in
@[simp] theorem sesqForm_neg_right (H : Matrix n n D) (x y : n → D) :
    σ.sesqForm H x (-y) = -σ.sesqForm H x y := by
  simp only [sesqForm, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

@[simp] theorem sesqForm_sub_left (H : Matrix n n D) (x x' y : n → D) :
    σ.sesqForm H (x - x') y = σ.sesqForm H x y - σ.sesqForm H x' y := by
  rw [sub_eq_add_neg, σ.sesqForm_add_left, sesqForm_neg_left, ← sub_eq_add_neg]

@[simp] theorem sesqForm_sub_right (H : Matrix n n D) (x y y' : n → D) :
    σ.sesqForm H x (y - y') = σ.sesqForm H x y - σ.sesqForm H x y' := by
  rw [sub_eq_add_neg, σ.sesqForm_add_right, sesqForm_neg_right, ← sub_eq_add_neg]

omit [DecidableEq n] in
theorem sesqForm_sub_matrix (H H' : Matrix n n D) (x y : n → D) :
    σ.sesqForm (H - H') x y = σ.sesqForm H x y - σ.sesqForm H' x y := by
  simp only [sesqForm, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq n] in
theorem sesqForm_zero_matrix (x y : n → D) : σ.sesqForm (0 : Matrix n n D) x y = 0 := by
  simp [sesqForm]

/-- The entries of a Gram matrix are the values of its form on standard basis vectors. -/
theorem sesqForm_single_single (H : Matrix n n D) (i j : n) :
    σ.sesqForm H (Pi.single i 1) (Pi.single j 1) = H i j := by
  rw [σ.sesqForm_eq_dotProduct, single_dotProduct, one_mul]
  have : (σ ∘ Pi.single j (1 : D)) = Pi.single j 1 := by
    ext k
    by_cases h : k = j
    · subst h
      simp
    · simp [h]
  rw [this, mulVec_single]
  simp

/-- A Gram matrix is determined by its sesquilinear form. -/
theorem matrix_eq_of_sesqForm_eq {H H' : Matrix n n D}
    (h : ∀ x y, σ.sesqForm H x y = σ.sesqForm H' x y) : H = H' := by
  ext i j
  rw [← sesqForm_single_single σ H i j, ← sesqForm_single_single σ H' i j, h]

/-! ### Quadratic values and polar forms -/

/-- An element of Tits's subspace has alternating values. -/
theorem sesqForm_self_mem_of_mem_quadraticKernel {M : Matrix n n D}
    (hM : M ∈ σ.quadraticKernel n) (x : n → D) :
    σ.sesqForm M x x ∈ σ.alternatingSubspace := by
  obtain ⟨X, rfl⟩ := (σ.matrix n).mem_alternatingSubspace.1 hM
  rw [sesqForm_sub_matrix, ← map_sesqForm_self]
  exact σ.sub_mem_alternatingSubspace _

/-- An element of Tits's subspace is `σ`-antihermitian. -/
theorem add_matrix_eq_zero_of_mem_quadraticKernel {M : Matrix n n D}
    (hM : M ∈ σ.quadraticKernel n) : M + σ.matrix n M = 0 :=
  add_map_eq_zero_of_mem_alternatingSubspace (σ.matrix n) hM

/-- A `σ`-antihermitian matrix with alternating diagonal lies in Tits's subspace. -/
theorem mem_quadraticKernel_of_antihermitian [LinearOrder n] {M : Matrix n n D}
    (hM : σ.matrix n M = -M) (hdiag : ∀ i, M i i ∈ σ.alternatingSubspace) :
    M ∈ σ.quadraticKernel n := by
  choose a ha using fun i => σ.mem_alternatingSubspace.1 (hdiag i)
  refine (σ.matrix n).mem_alternatingSubspace.2
    ⟨Matrix.of fun i j => if i < j then M i j else if i = j then a i else 0, ?_⟩
  ext i j
  have hji : σ (M j i) = -M i j := by
    have := congrFun (congrFun hM i) j
    simpa using this
  simp only [Matrix.sub_apply, matrix_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij, hij.ne', not_lt.2 hij.le]
  · simp [ha]
  · simp [hij, hij.ne', not_lt.2 hij.le, hji]

/-! ### Rational isometries -/

/-- The rational isometries of `q`: units `u` of `M_n(D)` with `u Q ᵗu^σ - Q` in Tits's
subspace `{x - ᵗx^σ}`, for the chosen representative `Q = Quotient.out q`. -/
def rationalIsometryGroup (q : σ.QuadraticForms n) : Subgroup (Matrix n n D)ˣ where
  carrier := {u | (u : Matrix n n D) * Quotient.out q * σ.matrix n u - Quotient.out q ∈
    σ.quadraticKernel n}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, one_mul, map_one, mul_one, sub_self]
    exact Submodule.zero_mem _
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at hx hy ⊢
    set Q := Quotient.out q
    have hstab : (x : Matrix n n D) * ((y : Matrix n n D) * Q * σ.matrix n y - Q) *
        σ.matrix n x ∈ σ.quadraticKernel n :=
      mul_mul_map_mem_alternatingSubspace (σ.matrix n) hy _
    have hsum := Submodule.add_mem _ hstab hx
    have e : (x : Matrix n n D) * y * Q * (σ.matrix n y * σ.matrix n x) - Q =
        (x : Matrix n n D) * ((y : Matrix n n D) * Q * σ.matrix n y - Q) * σ.matrix n x +
          ((x : Matrix n n D) * Q * σ.matrix n x - Q) := by
      noncomm_ring
    rw [e]
    exact hsum
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    set Q := Quotient.out q
    set a : Matrix n n D := ((x⁻¹ : (Matrix n n D)ˣ) : Matrix n n D)
    have h1 : a * (x : Matrix n n D) = 1 := Units.inv_mul x
    have h2 : σ.matrix n (x : Matrix n n D) * σ.matrix n a = 1 := by
      rw [← map_mul, h1, map_one]
    obtain ⟨X, hX⟩ := (σ.matrix n).mem_alternatingSubspace.1 hx
    refine (σ.matrix n).mem_alternatingSubspace.2 ⟨-(a * X * σ.matrix n a), ?_⟩
    have key : a * Q * σ.matrix n a - Q =
        -(a * ((x : Matrix n n D) * Q * σ.matrix n x - Q) * σ.matrix n a) := by
      calc a * Q * σ.matrix n a - Q
          = a * Q * σ.matrix n a - (a * x) * Q * (σ.matrix n x * σ.matrix n a) := by
            rw [h1, h2, one_mul, mul_one]
        _ = -(a * ((x : Matrix n n D) * Q * σ.matrix n x - Q) * σ.matrix n a) := by
            noncomm_ring
    rw [key, ← hX]
    simp only [map_neg, map_mul, apply_apply]
    noncomm_ring

/-- Membership in the rational isometry group can be tested on any representative. -/
theorem mem_rationalIsometryGroup_iff (q : σ.QuadraticForms n) (Q : Matrix n n D)
    (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms n) = q) (u : (Matrix n n D)ˣ) :
    u ∈ rationalIsometryGroup σ q ↔
      (u : Matrix n n D) * Q * σ.matrix n u - Q ∈ σ.quadraticKernel n := by
  change _ ∈ σ.quadraticKernel n ↔ _
  have hmem : Quotient.out q - Q ∈ σ.quadraticKernel n := by
    rw [← Submodule.Quotient.eq]
    exact (Submodule.Quotient.mk_out q).trans hQ.symm
  have hstab : (u : Matrix n n D) * (Quotient.out q - Q) * σ.matrix n u ∈
      σ.quadraticKernel n :=
    mul_mul_map_mem_alternatingSubspace (σ.matrix n) hmem _
  have hd : ((u : Matrix n n D) * Quotient.out q * σ.matrix n u - Quotient.out q) -
      ((u : Matrix n n D) * Q * σ.matrix n u - Q) ∈ σ.quadraticKernel n := by
    have := Submodule.sub_mem _ hstab hmem
    convert this using 1
    noncomm_ring
  constructor
  · intro h
    have := Submodule.sub_mem _ h hd
    rwa [sub_sub_cancel] at this
  · intro h
    have := Submodule.add_mem _ hd h
    rwa [sub_add_cancel] at this

/-- A rational isometry preserves the polar form. -/
theorem sesqForm_polar_vecMul_of_mem (q : σ.QuadraticForms n) {u : (Matrix n n D)ˣ}
    (hu : u ∈ rationalIsometryGroup σ q) (x y : n → D) :
    σ.sesqForm (σ.polar q) (x ᵥ* (u : Matrix n n D)) (y ᵥ* (u : Matrix n n D)) =
      σ.sesqForm (σ.polar q) x y := by
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [mem_rationalIsometryGroup_iff σ _ Q rfl] at hu
  have h0 := add_matrix_eq_zero_of_mem_quadraticKernel σ hu
  rw [σ.sesqForm_vecMul, polar_mk]
  congr 1
  have : (u : Matrix n n D) * Q * σ.matrix n u + σ.matrix n
      ((u : Matrix n n D) * Q * σ.matrix n u) = Q + σ.matrix n Q := by
    rw [← sub_eq_zero, ← h0]
    simp only [map_sub]
    abel
  refine Eq.trans ?_ this
  simp only [map_mul, apply_apply]
  noncomm_ring

/-- A rational isometry preserves quadratic values. -/
theorem quadraticValue_vecMul_of_mem (q : σ.QuadraticForms n) {u : (Matrix n n D)ˣ}
    (hu : u ∈ rationalIsometryGroup σ q) (x : n → D) :
    σ.quadraticValue (x ᵥ* (u : Matrix n n D)) q = σ.quadraticValue x q := by
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [mem_rationalIsometryGroup_iff σ _ Q rfl] at hu
  rw [quadraticValue_mk, quadraticValue_mk, Submodule.Quotient.eq, σ.sesqForm_vecMul,
    ← sesqForm_sub_matrix]
  exact sesqForm_self_mem_of_mem_quadraticKernel σ hu x

/-- **Isometry criterion.** Over a linearly ordered index type, a unit is a rational isometry
of `q = [Q]` as soon as it preserves the polar form and the values `Q(x, x)` modulo the
alternating subspace. -/
theorem mem_rationalIsometryGroup_of_forall [LinearOrder n] (Q : Matrix n n D)
    (u : (Matrix n n D)ˣ)
    (hpolar : ∀ x y, σ.sesqForm (Q + σ.matrix n Q) (x ᵥ* (u : Matrix n n D))
      (y ᵥ* (u : Matrix n n D)) = σ.sesqForm (Q + σ.matrix n Q) x y)
    (hvalue : ∀ x, σ.sesqForm Q (x ᵥ* (u : Matrix n n D)) (x ᵥ* (u : Matrix n n D)) -
      σ.sesqForm Q x x ∈ σ.alternatingSubspace) :
    u ∈ rationalIsometryGroup σ (Submodule.Quotient.mk Q) := by
  rw [mem_rationalIsometryGroup_iff σ _ Q rfl]
  set M := (u : Matrix n n D) * Q * σ.matrix n u - Q
  apply mem_quadraticKernel_of_antihermitian σ
  · have hH : (u : Matrix n n D) * (Q + σ.matrix n Q) * σ.matrix n u = Q + σ.matrix n Q :=
      matrix_eq_of_sesqForm_eq σ fun x y => by rw [← σ.sesqForm_vecMul, hpolar]
    have : M + σ.matrix n M = 0 := by
      simp only [M, map_sub, map_mul, apply_apply]
      rw [← sub_eq_zero.2 hH]
      noncomm_ring
    exact eq_neg_of_add_eq_zero_right this
  · intro i
    have := hvalue (Pi.single i 1)
    rwa [σ.sesqForm_vecMul, ← sesqForm_sub_matrix, sesqForm_single_single] at this

/-- **Isometry criterion**, intrinsic form: over a linearly ordered index type, a unit is a
rational isometry of `q` exactly when it preserves the polar form and the values of `q`. -/
theorem mem_rationalIsometryGroup_iff_forall [LinearOrder n] (q : σ.QuadraticForms n)
    (u : (Matrix n n D)ˣ) :
    u ∈ rationalIsometryGroup σ q ↔
      (∀ x y, σ.sesqForm (σ.polar q) (x ᵥ* (u : Matrix n n D)) (y ᵥ* (u : Matrix n n D)) =
        σ.sesqForm (σ.polar q) x y) ∧
      ∀ x, σ.quadraticValue (x ᵥ* (u : Matrix n n D)) q = σ.quadraticValue x q := by
  refine ⟨fun hu => ⟨sesqForm_polar_vecMul_of_mem σ q hu,
    quadraticValue_vecMul_of_mem σ q hu⟩, fun ⟨hpolar, hvalue⟩ => ?_⟩
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine mem_rationalIsometryGroup_of_forall σ Q u (fun x y => ?_) (fun x => ?_)
  · simpa only [polar_mk] using hpolar x y
  · have := hvalue x
    rwa [quadraticValue_mk, quadraticValue_mk, Submodule.Quotient.eq] at this

end FirstKindInvolution.Eichler

end Langlands.GroupScheme.Quaternionic
