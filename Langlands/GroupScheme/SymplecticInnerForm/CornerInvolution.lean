import Langlands.GroupScheme.SymplecticInnerForm.EpsilonHermitian
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Involutions of matrix algebras over division rings as adjoint involutions

Let `D` be a division ring which is an algebra over a field `K`, and let `τ` be an involution
of the first kind of `B = M_ι(D)`. This module constructs an involution of the first kind `θ`
of `D`, a scalar `ε` with `ε * ε = 1` and a unit `U ∈ B` with inverse `U'` such that

`τ y = U * ᵗy^θ * U'` for every `y`, and `ᵗU^θ = ε • U`.

The construction is a corner computation. Put `e = E_{i₀i₀}` and `f = τ e`. A nonzero
element `w ∈ e B f` with `τ w = ε • w` has a quasi-inverse `w' ∈ f B e`, with
`w * w' = e` and `w' * w = f`. Then `θ a` is the `(i₀, i₀)` entry of `w τ(E_{i₀i₀}(a)) w'`,
and `U = ∑ k, τ(E_{i₀k}) w' E_{i₀k}`. Replacing `w` by `E_{i₀i₀}(v) w`, for `v ≠ 0` with
`θ v = -v`, changes `ε = 1` into `ε = -1`.
-/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  {ι : Type w} [Fintype ι] [DecidableEq ι]

section Single

variable (i₀ : ι)

theorem single_one_mul_mul_single_one (x : Matrix ι ι D) :
    single i₀ i₀ (1 : D) * x * single i₀ i₀ 1 = single i₀ i₀ (x i₀ i₀) := by
  rw [single_mul_mul_single, one_mul, mul_one]

theorem eq_single_of_corner {x : Matrix ι ι D} (h1 : single i₀ i₀ 1 * x = x)
    (h2 : x * single i₀ i₀ 1 = x) : x = single i₀ i₀ (x i₀ i₀) :=
  calc x = single i₀ i₀ 1 * x * single i₀ i₀ 1 := by rw [h1, h2]
    _ = single i₀ i₀ (x i₀ i₀) := single_one_mul_mul_single_one i₀ x

omit [Fintype ι] in
theorem single_diag_injective {a b : D} (h : single i₀ i₀ a = single i₀ i₀ b) : a = b := by
  simpa using congrFun (congrFun h i₀) i₀

/-- The conjugate transpose of a matrix unit. -/
theorem matrix_single (θ : FirstKindInvolution K D) (i j : ι) (a : D) :
    θ.matrix ι (single i j a) = single j i (θ a) := by
  ext k l
  by_cases h : i = l ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [matrix_apply, single_apply_of_ne _ _ _ _ _ h, map_zero,
      single_apply_of_ne _ _ _ _ _ fun h' => h ⟨h'.2, h'.1⟩]

end Single

section Corner

variable (τ : FirstKindInvolution K (Matrix ι ι D)) (i₀ : ι)

theorem map_single_mul_map_single :
    τ (single i₀ i₀ (1 : D)) * τ (single i₀ i₀ 1) = τ (single i₀ i₀ 1) := by
  rw [← map_mul, single_mul_single_same, one_mul]

/-- `x` lies in the corner `e B f`, where `e = E_{i₀i₀}` and `f = τ e`. -/
def IsCorner (x : Matrix ι ι D) : Prop :=
  single i₀ i₀ 1 * x = x ∧ x * τ (single i₀ i₀ 1) = x

variable {τ i₀}

theorem IsCorner.map {x : Matrix ι ι D} (hx : IsCorner τ i₀ x) : IsCorner τ i₀ (τ x) := by
  constructor
  · calc single i₀ i₀ 1 * τ x = τ (τ (single i₀ i₀ 1)) * τ x := by rw [apply_apply]
      _ = τ x := by rw [← map_mul, hx.2]
  · rw [← map_mul, hx.1]

theorem IsCorner.apply_eq_zero {x : Matrix ι ι D} (hx : IsCorner τ i₀ x) {i : ι} (hi : i ≠ i₀)
    (j : ι) : x i j = 0 := by
  rw [← hx.1, single_mul_apply_of_ne _ _ _ _ _ hi]

theorem IsCorner.exists_ne_zero {x : Matrix ι ι D} (hx : IsCorner τ i₀ x) (hx0 : x ≠ 0) :
    ∃ q, x i₀ q ≠ 0 := by
  by_contra h
  push Not at h
  apply hx0
  ext i j
  by_cases hi : i = i₀
  · subst hi
    exact h j
  · exact hx.apply_eq_zero hi j

variable (τ i₀)

theorem exists_isCorner_ne_zero : ∃ x, IsCorner τ i₀ x ∧ x ≠ 0 := by
  have hf : τ (single i₀ i₀ (1 : D)) ≠ 0 := by
    intro h
    have h' : single i₀ i₀ (1 : D) = 0 := τ.injective (h.trans τ.map_zero.symm)
    have := congrFun (congrFun h' i₀) i₀
    simp at this
  obtain ⟨p, q, hpq⟩ : ∃ p q, τ (single i₀ i₀ (1 : D)) p q ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Matrix.ext h)
  refine ⟨single i₀ p 1 * τ (single i₀ i₀ 1), ⟨?_, ?_⟩, ?_⟩
  · rw [← mul_assoc, single_mul_single_same, one_mul]
  · rw [mul_assoc, map_single_mul_map_single]
  · intro h
    have := congrFun (congrFun h i₀) q
    rw [single_mul_apply_same, one_mul] at this
    exact hpq this

theorem exists_isCorner_eps :
    ∃ (x : Matrix ι ι D) (ε : K), IsCorner τ i₀ x ∧ x ≠ 0 ∧ ε * ε = 1 ∧ τ x = ε • x := by
  obtain ⟨x, hx, hx0⟩ := exists_isCorner_ne_zero τ i₀
  by_cases h : x + τ x = 0
  · refine ⟨x, -1, hx, hx0, by norm_num, ?_⟩
    rw [neg_one_smul]
    exact eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans h)
  · refine ⟨x + τ x, 1, ⟨?_, ?_⟩, h, by norm_num, ?_⟩
    · rw [mul_add, hx.1, hx.map.1]
    · rw [add_mul, hx.2, hx.map.2]
    · rw [one_smul, map_add, apply_apply, add_comm]

variable {τ i₀}

/-- A nonzero corner element has a quasi-inverse `x' ∈ f B e` with `x x' = e`, `x' x = f`. -/
theorem IsCorner.exists_quasiInverse {x : Matrix ι ι D} (hx : IsCorner τ i₀ x) (hx0 : x ≠ 0) :
    ∃ x', x' * single i₀ i₀ 1 = x' ∧ x * x' = single i₀ i₀ 1 ∧
      x' * x = τ (single i₀ i₀ 1) := by
  obtain ⟨q, hq⟩ := hx.exists_ne_zero hx0
  set x' := τ (single i₀ i₀ 1) * single q i₀ (x i₀ q)⁻¹ with hx'
  have h1 : x' * single i₀ i₀ 1 = x' := by
    rw [hx', mul_assoc, single_mul_single_same, mul_one]
  have h2 : x * x' = single i₀ i₀ 1 := by
    rw [hx', ← mul_assoc, hx.2]
    ext i j
    by_cases hj : j = i₀
    · subst hj
      rw [mul_single_apply_same]
      by_cases hi : i = j
      · subst hi
        rw [mul_inv_cancel₀ hq, single_apply_same]
      · rw [hx.apply_eq_zero hi, zero_mul, single_apply_of_row_ne (Ne.symm hi)]
    · rw [mul_single_apply_of_ne _ _ _ _ _ hj, single_apply_of_col_ne _ _ (Ne.symm hj)]
  refine ⟨x', h1, h2, ?_⟩
  have hfx' : τ (single i₀ i₀ 1) * x' = x' := by
    rw [hx', ← mul_assoc, map_single_mul_map_single]
  have hfp : τ (single i₀ i₀ 1) * (x' * x) = x' * x := by rw [← mul_assoc, hfx']
  have hpf : x' * x * τ (single i₀ i₀ 1) = x' * x := by rw [mul_assoc, hx.2]
  have hpp : x' * x * (x' * x) = x' * x := by
    rw [mul_assoc, ← mul_assoc x x', h2, ← mul_assoc, h1]
  have hp0 : x' * x ≠ 0 := by
    intro h
    apply hx0
    calc x = single i₀ i₀ 1 * x := hx.1.symm
      _ = x * (x' * x) := by rw [← mul_assoc, h2]
      _ = 0 := by rw [h, mul_zero]
  have hτ1 : single i₀ i₀ 1 * τ (x' * x) = τ (x' * x) := by
    calc single i₀ i₀ 1 * τ (x' * x) = τ (τ (single i₀ i₀ 1)) * τ (x' * x) := by
          rw [apply_apply]
      _ = τ (x' * x) := by rw [← map_mul, hpf]
  have hτ2 : τ (x' * x) * single i₀ i₀ 1 = τ (x' * x) := by
    calc τ (x' * x) * single i₀ i₀ 1 = τ (x' * x) * τ (τ (single i₀ i₀ 1)) := by
          rw [apply_apply]
      _ = τ (x' * x) := by rw [← map_mul, hfp]
  have hs := eq_single_of_corner i₀ hτ1 hτ2
  set a := τ (x' * x) i₀ i₀
  have ha : a * a = a := by
    apply single_diag_injective i₀
    have hsq : single i₀ i₀ (a * a) = single i₀ i₀ a * single i₀ i₀ a := by
      rw [single_mul_single_same]
    rw [hsq, ← hs, ← map_mul, hpp]
  have ha0 : a ≠ 0 := by
    intro h
    apply hp0
    apply τ.injective
    rw [hs, h, single_zero, map_zero]
  have ha1 : a = 1 := mul_left_cancel₀ ha0 (ha.trans (mul_one a).symm)
  calc x' * x = τ (τ (x' * x)) := (apply_apply _ _).symm
    _ = τ (single i₀ i₀ 1) := by rw [hs, ha1]

end Corner

/-- The data of a corner element: `w ∈ e B f` with `τ w = ε • w` and a quasi-inverse
`w' ∈ f B e`, where `e = E_{i₀i₀}` and `f = τ e`. -/
structure CornerData (τ : FirstKindInvolution K (Matrix ι ι D)) (i₀ : ι) where
  /-- The corner element. -/
  w : Matrix ι ι D
  /-- Its quasi-inverse. -/
  w' : Matrix ι ι D
  /-- The symmetry sign. -/
  ε : K
  ε_mul_self : ε * ε = 1
  single_mul_w : single i₀ i₀ 1 * w = w
  w'_mul_single : w' * single i₀ i₀ 1 = w'
  w_mul_w' : w * w' = single i₀ i₀ 1
  w'_mul_w : w' * w = τ (single i₀ i₀ 1)
  map_w : τ w = ε • w

theorem exists_cornerData {τ : FirstKindInvolution K (Matrix ι ι D)} {i₀ : ι}
    {x : Matrix ι ι D} {ε : K} (hx : IsCorner τ i₀ x) (hx0 : x ≠ 0) (hε : ε * ε = 1)
    (hτx : τ x = ε • x) : ∃ c : CornerData τ i₀, c.w = x ∧ c.ε = ε := by
  obtain ⟨x', h1, h2, h3⟩ := hx.exists_quasiInverse hx0
  exact ⟨⟨x, x', ε, hε, hx.1, h1, h2, h3, hτx⟩, rfl, rfl⟩

namespace CornerData

variable {τ : FirstKindInvolution K (Matrix ι ι D)} {i₀ : ι} (c : CornerData τ i₀)

theorem w_mul_f : c.w * τ (single i₀ i₀ 1) = c.w := by
  rw [← c.w'_mul_w, ← mul_assoc, c.w_mul_w', c.single_mul_w]

theorem f_mul_w' : τ (single i₀ i₀ 1) * c.w' = c.w' := by
  rw [← c.w'_mul_w, mul_assoc, c.w_mul_w', c.w'_mul_single]

theorem w_ne_zero : c.w ≠ 0 := by
  intro h
  have := congrFun (congrFun c.w_mul_w' i₀) i₀
  rw [h, zero_mul] at this
  simp at this

theorem map_w' : τ c.w' = c.ε • c.w' := by
  have hfy : τ (single i₀ i₀ 1) * (c.ε • τ c.w') = c.ε • τ c.w' := by
    rw [mul_smul_comm, ← map_mul, c.w'_mul_single]
  have hwy : c.w * (c.ε • τ c.w') = single i₀ i₀ 1 := by
    rw [mul_smul_comm, ← smul_mul_assoc, ← c.map_w, ← map_mul, c.w'_mul_w, apply_apply]
  have hy : c.ε • τ c.w' = c.w' := by
    calc c.ε • τ c.w' = τ (single i₀ i₀ 1) * (c.ε • τ c.w') := hfy.symm
      _ = c.w' * (c.w * (c.ε • τ c.w')) := by rw [← mul_assoc, c.w'_mul_w]
      _ = c.w' := by rw [hwy, c.w'_mul_single]
  calc τ c.w' = (c.ε * c.ε) • τ c.w' := by rw [c.ε_mul_self, one_smul]
    _ = c.ε • c.w' := by rw [mul_smul, hy]

theorem corner_mem (a : D) :
    c.w * τ (single i₀ i₀ a) * c.w' =
      single i₀ i₀ ((c.w * τ (single i₀ i₀ a) * c.w') i₀ i₀) :=
  eq_single_of_corner i₀ (by rw [← mul_assoc, ← mul_assoc, c.single_mul_w])
    (by rw [mul_assoc, c.w'_mul_single])

/-- The involution of `D` cut out by the corner element: `θ a` is the `(i₀, i₀)` entry of
`w τ(E_{i₀i₀}(a)) w'`. -/
def involution : FirstKindInvolution K D where
  toLinearMap :=
    { toFun := fun a => (c.w * τ (single i₀ i₀ a) * c.w') i₀ i₀
      map_add' := fun a b => by
        simp only [single_add, map_add, mul_add, add_mul, add_apply]
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        rw [← smul_single, map_smul, mul_smul_comm, smul_mul_assoc, smul_apply] }
  map_one' := by
    show (c.w * τ (single i₀ i₀ 1) * c.w') i₀ i₀ = 1
    rw [c.w_mul_f, c.w_mul_w', single_apply_same]
  map_mul' := fun a b => by
    change (c.w * τ (single i₀ i₀ (a * b)) * c.w') i₀ i₀ =
      (c.w * τ (single i₀ i₀ b) * c.w') i₀ i₀ * (c.w * τ (single i₀ i₀ a) * c.w') i₀ i₀
    have hab : single i₀ i₀ (a * b) = single i₀ i₀ a * single i₀ i₀ b := by
      rw [single_mul_single_same]
    have hb : τ (single i₀ i₀ b) * τ (single i₀ i₀ 1) = τ (single i₀ i₀ b) := by
      rw [← map_mul, single_mul_single_same, one_mul]
    have key : c.w * τ (single i₀ i₀ (a * b)) * c.w' =
        c.w * τ (single i₀ i₀ b) * c.w' * (c.w * τ (single i₀ i₀ a) * c.w') :=
      calc c.w * τ (single i₀ i₀ (a * b)) * c.w' =
          c.w * (τ (single i₀ i₀ b) * τ (single i₀ i₀ 1) * τ (single i₀ i₀ a)) * c.w' := by
            rw [hb, hab, map_mul]
        _ = c.w * τ (single i₀ i₀ b) * c.w' * (c.w * τ (single i₀ i₀ a) * c.w') := by
            rw [← c.w'_mul_w]
            simp only [mul_assoc]
    conv_lhs => rw [key, c.corner_mem b, c.corner_mem a]
    rw [single_mul_single_same, single_apply_same]
  involutive' := fun a => by
    change (c.w * τ (single i₀ i₀ ((c.w * τ (single i₀ i₀ a) * c.w') i₀ i₀)) * c.w') i₀ i₀ = a
    have h : c.w * τ (c.w * τ (single i₀ i₀ a) * c.w') * c.w' = single i₀ i₀ a := by
      rw [map_mul, map_mul, apply_apply, c.map_w, c.map_w']
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, c.ε_mul_self, one_smul]
      simp only [mul_assoc]
      rw [c.w_mul_w', single_mul_single_same, mul_one, ← mul_assoc, c.w_mul_w',
        single_mul_single_same, one_mul]
    rw [← c.corner_mem a, h, single_apply_same]

theorem involution_apply (a : D) :
    c.involution a = (c.w * τ (single i₀ i₀ a) * c.w') i₀ i₀ :=
  rfl

theorem corner_eq (a : D) :
    c.w * τ (single i₀ i₀ a) * c.w' = single i₀ i₀ (c.involution a) :=
  c.corner_mem a

/-- `τ (E_{i₀i₀}(a)) = w' E_{i₀i₀}(θ a) w`. -/
theorem map_single (a : D) :
    τ (single i₀ i₀ a) = c.w' * single i₀ i₀ (c.involution a) * c.w := by
  rw [← c.corner_eq]
  have h : τ (single i₀ i₀ a) = c.w' * c.w * τ (single i₀ i₀ a) * (c.w' * c.w) := by
    rw [c.w'_mul_w, ← map_mul, ← map_mul, single_mul_single_same, single_mul_single_same,
      one_mul, mul_one]
  conv_lhs => rw [h]
  simp only [mul_assoc]

theorem w_mul_map_single (a : D) :
    c.w * τ (single i₀ i₀ a) = single i₀ i₀ (c.involution a) * c.w := by
  rw [c.map_single, ← mul_assoc, ← mul_assoc, c.w_mul_w', single_mul_single_same, one_mul]

/-- The Gram matrix `U = ∑ k, τ(E_{i₀k}) w' E_{i₀k}`. -/
def gram : Matrix ι ι D :=
  ∑ k, τ (single i₀ k 1) * c.w' * single i₀ k 1

/-- The inverse Gram matrix `U' = ∑ k, E_{ki₀} w τ(E_{ki₀})`. -/
def gramInv : Matrix ι ι D :=
  ∑ k, single k i₀ 1 * c.w * τ (single k i₀ 1)

theorem gram_mul_single (j i : ι) (b : D) :
    c.gram * single j i b = τ (single i₀ j 1) * c.w' * single i₀ i b := by
  rw [gram, Finset.sum_mul, Finset.sum_eq_single j]
  · rw [mul_assoc, single_mul_single_same, one_mul]
  · intro k _ hk
    rw [mul_assoc, single_mul_single_of_ne _ _ _ _ hk, mul_zero]
  · simp

theorem single_mul_gramInv (i : ι) (b : D) :
    single i₀ i b * c.gramInv = single i₀ i₀ b * c.w * τ (single i i₀ 1) := by
  rw [gramInv, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [← mul_assoc, ← mul_assoc, single_mul_single_same, mul_one]
  · intro k _ hk
    rw [← mul_assoc, ← mul_assoc, single_mul_single_of_ne _ _ _ _ (Ne.symm hk), zero_mul,
      zero_mul]
  · simp

theorem map_single_eq_gram (i j : ι) (a : D) :
    τ (single i j a) = c.gram * c.involution.matrix ι (single i j a) * c.gramInv := by
  rw [matrix_single, c.gram_mul_single, mul_assoc, c.single_mul_gramInv]
  calc τ (single i j a) = τ (single i i₀ 1 * single i₀ i₀ a * single i₀ j 1) := by
        rw [single_mul_single_same, single_mul_single_same, one_mul, mul_one]
    _ = τ (single i₀ j 1) * τ (single i₀ i₀ a) * τ (single i i₀ 1) := by
        rw [map_mul, map_mul, ← mul_assoc]
    _ = _ := by
        rw [c.map_single]
        simp only [mul_assoc]

theorem map_eq_gram (y : Matrix ι ι D) :
    τ y = c.gram * c.involution.matrix ι y * c.gramInv := by
  conv_lhs => rw [matrix_eq_sum_single y]
  conv_rhs => rw [matrix_eq_sum_single y]
  simp only [FirstKindInvolution.map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact c.map_single_eq_gram i j (y i j)

theorem gram_mul_gramInv : c.gram * c.gramInv = 1 := by
  have h := c.map_eq_gram 1
  rw [FirstKindInvolution.map_one, FirstKindInvolution.map_one, mul_one] at h
  exact h.symm

theorem gramInv_mul_gram : c.gramInv * c.gram = 1 :=
  mul_eq_one_symm c.gram_mul_gramInv

theorem map_gram : τ c.gram = c.ε • c.gram := by
  rw [gram, FirstKindInvolution.map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, apply_apply, c.map_w', smul_mul_assoc, mul_smul_comm, mul_assoc]

theorem matrix_gram : c.involution.matrix ι c.gram = c.ε • c.gram := by
  have h : c.involution.matrix ι c.gram = c.gramInv * τ c.gram * c.gram := by
    rw [c.map_eq_gram c.gram, ← mul_assoc, ← mul_assoc, c.gramInv_mul_gram, one_mul,
      mul_assoc, c.gramInv_mul_gram, mul_one]
  rw [h, c.map_gram, mul_smul_comm, smul_mul_assoc, c.gramInv_mul_gram, one_mul]

end CornerData

variable (τ : FirstKindInvolution K (Matrix ι ι D))

/-- `τ = Int(U) ∘ θ*`: `τ y = U ᵗy^θ U'` with `U U' = 1 = U' U` and `ᵗU^θ = ε • U`,
`ε * ε = 1`. -/
def IsGramModel (θ : FirstKindInvolution K D) (ε : K) (U U' : Matrix ι ι D) : Prop :=
  ε * ε = 1 ∧ U * U' = 1 ∧ U' * U = 1 ∧ θ.matrix ι U = ε • U ∧
    ∀ y, τ y = U * θ.matrix ι y * U'

theorem CornerData.isGramModel {i₀ : ι} (c : CornerData τ i₀) :
    IsGramModel τ c.involution c.ε c.gram c.gramInv :=
  ⟨c.ε_mul_self, c.gram_mul_gramInv, c.gramInv_mul_gram, c.matrix_gram, c.map_eq_gram⟩

/-- Every involution of the first kind of `M_ι(D)` is `Int(U) ∘ θ*` for an involution of the
first kind `θ` of `D`. If the sign is `1` and `θ` has a nonzero skew element, the
construction can be redone with sign `-1`. -/
theorem exists_isGramModel [Nonempty ι] :
    ∃ (θ : FirstKindInvolution K D) (ε : K) (U U' : Matrix ι ι D),
      IsGramModel τ θ ε U U' ∧
        (ε = 1 → ∀ v : D, v ≠ 0 → θ v = -v →
          ∃ (θ' : FirstKindInvolution K D) (U₂ U₂' : Matrix ι ι D),
            IsGramModel τ θ' (-1) U₂ U₂') := by
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨x, ε, hx, hx0, hε, hτx⟩ := exists_isCorner_eps τ i₀
  obtain ⟨c, rfl, rfl⟩ := exists_cornerData hx hx0 hε hτx
  refine ⟨c.involution, c.ε, c.gram, c.gramInv, c.isGramModel τ, ?_⟩
  intro h1 v hv hθv
  have hc2 : IsCorner τ i₀ (single i₀ i₀ v * c.w) :=
    ⟨by rw [← mul_assoc, single_mul_single_same, one_mul], by rw [mul_assoc, c.w_mul_f]⟩
  have hc20 : single i₀ i₀ v * c.w ≠ 0 := by
    intro h
    apply c.w_ne_zero
    calc c.w = single i₀ i₀ 1 * c.w := c.single_mul_w.symm
      _ = single i₀ i₀ v⁻¹ * (single i₀ i₀ v * c.w) := by
          rw [← mul_assoc, single_mul_single_same, inv_mul_cancel₀ hv]
      _ = 0 := by rw [h, mul_zero]
  have hτ2 : τ (single i₀ i₀ v * c.w) = (-1 : K) • (single i₀ i₀ v * c.w) := by
    rw [map_mul, c.map_w, h1, one_smul, c.w_mul_map_single, hθv, ← single_neg, neg_mul,
      neg_one_smul]
  obtain ⟨c₂, -, hε₂⟩ := exists_cornerData hc2 hc20 (by norm_num) hτ2
  refine ⟨c₂.involution, c₂.gram, c₂.gramInv, ?_⟩
  rw [← hε₂]
  exact c₂.isGramModel τ

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
