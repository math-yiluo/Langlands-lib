import Langlands.GroupScheme.Quaternionic.EichlerTransformations
import Langlands.GroupScheme.Quaternionic.AntihermitianWittBasis
import Langlands.GroupScheme.Quaternionic.HyperbolicBasis

/-! # Line rotations of antihermitian forms over a division algebra

Let `τ` be an involution of the first kind of a division algebra `A` over a field `K` and `G`
an antihermitian Gram matrix, with form `h(x, y) = ∑ x i G i j τ(y j)` on row vectors. For a
row `a` with `c = h(a, a) ≠ 0` and `e ∈ A`, the matrix `lineMatrix τ G a e` acts by
`v ↦ v + h(v, a) c⁻¹ (e - 1) a`: it multiplies `a` on the left by `e` and fixes the
orthogonal complement of `a`. These matrices compose by multiplying the parameters, and they
preserve `h` exactly when `e c τ(e) = c`.

Two rows `x, y` with `h(x, x) = h(y, y)` are related by such a matrix along `a = x - y` with
parameter `τ(s) s⁻¹`, `s = h(x, a)`, when `s` is not fixed by `τ` (a unitary reflection).

Suppose `x τ(x) = N(x)` is scalar-valued and `K` has characteristic zero. If every element of
`K` or its negative is a square and sums of two squares are squares, the norm takes only square
values. If also `-1` is nonsquare, every parameter `e` with `e c τ(e) = c` has a square root
with the same property. Take `f = (1 + e)/r` with `r² = N(1 + e)` for `e ≠ -1`, and take
`f = c/r` with `r² = N(c)` for `e = -1`.
-/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution.LineRotation

variable {K : Type u} {A : Type v} [Field K] [DivisionRing A] [Algebra K A]
  (τ : FirstKindInvolution K A) {n : Type w} [Fintype n] [DecidableEq n] (G : Matrix n n A)

/-- The matrix of `v ↦ v + h(v, a) c⁻¹ (e - 1) a`, with `c = h(a, a)`. -/
def lineMatrix (a : n → A) (e : A) : Matrix n n A :=
  1 + vecMulVec (G *ᵥ (τ ∘ a)) (((τ.sesqForm G a a)⁻¹ * (e - 1)) • a)

theorem vecMul_lineMatrix (a : n → A) (e : A) (v : n → A) :
    v ᵥ* lineMatrix τ G a e =
      v + (τ.sesqForm G v a * ((τ.sesqForm G a a)⁻¹ * (e - 1))) • a := by
  rw [lineMatrix, vecMul_add, vecMul_one, vecMul_vecMulVec, ← τ.sesqForm_eq_dotProduct, smul_smul]

theorem vecMul_lineMatrix_of_orthogonal (a : n → A) (e : A) {v : n → A}
    (hv : τ.sesqForm G v a = 0) : v ᵥ* lineMatrix τ G a e = v := by
  rw [vecMul_lineMatrix, hv, zero_mul, zero_smul, add_zero]

theorem lineMatrix_one (a : n → A) : lineMatrix τ G a 1 = 1 := by
  rw [ext_iff_vecMul]
  intro v
  rw [vecMul_lineMatrix, sub_self, mul_zero, mul_zero, zero_smul, add_zero, vecMul_one]

theorem vecMul_lineMatrix_self {a : n → A} (hc : τ.sesqForm G a a ≠ 0) (e : A) :
    a ᵥ* lineMatrix τ G a e = e • a := by
  rw [vecMul_lineMatrix, mul_inv_cancel_left₀ hc, sub_smul, one_smul, add_sub_cancel]

/-- Line matrices along a fixed row compose by multiplying their parameters. -/
theorem lineMatrix_mul {a : n → A} (hc : τ.sesqForm G a a ≠ 0) (e e' : A) :
    lineMatrix τ G a e * lineMatrix τ G a e' = lineMatrix τ G a (e * e') := by
  rw [ext_iff_vecMul]
  intro v
  rw [← vecMul_vecMul, vecMul_lineMatrix, vecMul_lineMatrix, vecMul_lineMatrix,
    sesqForm_add_left, sesqForm_smul_left, add_assoc, ← add_smul]
  congr 2
  set c := τ.sesqForm G a a
  set β := τ.sesqForm G v a
  have hk : c⁻¹ * (e - 1) * c * (c⁻¹ * (e' - 1)) = c⁻¹ * ((e - 1) * (e' - 1)) := by
    simp only [mul_assoc, mul_inv_cancel_left₀ hc]
  calc β * (c⁻¹ * (e - 1)) + (β + β * (c⁻¹ * (e - 1)) * c) * (c⁻¹ * (e' - 1))
      = β * (c⁻¹ * (e - 1) + c⁻¹ * (e' - 1) + c⁻¹ * (e - 1) * c * (c⁻¹ * (e' - 1))) := by
        noncomm_ring
    _ = β * (c⁻¹ * (e * e' - 1)) := by rw [hk]; noncomm_ring

/-- On a line with `h(a, a) ≠ 0`, the inverse of the line matrix with nonzero parameter `e`
is the line matrix with parameter `e⁻¹`. -/
theorem lineMatrix_mul_inv {a : n → A} (hc : τ.sesqForm G a a ≠ 0) {e : A} (he : e ≠ 0) :
    lineMatrix τ G a e * lineMatrix τ G a e⁻¹ = 1 := by
  rw [lineMatrix_mul τ G hc, mul_inv_cancel₀ he, lineMatrix_one]

theorem lineMatrix_inv_mul {a : n → A} (hc : τ.sesqForm G a a ≠ 0) {e : A} (he : e ≠ 0) :
    lineMatrix τ G a e⁻¹ * lineMatrix τ G a e = 1 := by
  rw [lineMatrix_mul τ G hc, inv_mul_cancel₀ he, lineMatrix_one]

variable {τ G}

omit [Fintype n] [DecidableEq n] in
/-- The parameter identity behind the invariance of the form under a line matrix. -/
theorem lineParameter_identity {c e : A} (hc : c ≠ 0) (hτc : τ c = -c)
    (he : e * c * τ e = c) :
    τ (c⁻¹ * (e - 1)) - c⁻¹ * (e - 1) + c⁻¹ * (e - 1) * c * τ (c⁻¹ * (e - 1)) = 0 := by
  have hτk : τ (c⁻¹ * (e - 1)) = -((τ e - 1) * c⁻¹) := by
    rw [map_mul, map_sub, map_one, Eichler.map_inv_eq, hτc, inv_neg, mul_neg]
  have h1 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have h2 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have hmul : c * (τ (c⁻¹ * (e - 1)) - c⁻¹ * (e - 1) +
      c⁻¹ * (e - 1) * c * τ (c⁻¹ * (e - 1))) * c = 0 := by
    rw [hτk]
    calc c * (-((τ e - 1) * c⁻¹) - c⁻¹ * (e - 1) + c⁻¹ * (e - 1) * c * -((τ e - 1) * c⁻¹)) * c
        = -(c * (τ e - 1) * (c⁻¹ * c)) - (c * c⁻¹) * (e - 1) * c -
            (c * c⁻¹) * (e - 1) * c * (τ e - 1) * (c⁻¹ * c) := by noncomm_ring
      _ = c - e * c * τ e := by rw [h1, h2]; noncomm_ring
      _ = 0 := by rw [he, sub_self]
  rcases mul_eq_zero.mp hmul with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hc
    · exact h'
  · exact absurd h hc

theorem map_sesqForm_self_eq_neg (hG : τ.IsAntihermitian G) (x : n → A) :
    τ (τ.sesqForm G x x) = -τ.sesqForm G x x :=
  neg_eq_iff_eq_neg.mp (hG.sesqForm_swap τ x x).symm

/-- A line matrix with `c ≠ 0` preserves the antihermitian form when `e c τ(e) = c`. -/
theorem sesqForm_vecMul_lineMatrix (hG : τ.IsAntihermitian G) {a : n → A}
    (hc : τ.sesqForm G a a ≠ 0) {e : A} (he : e * τ.sesqForm G a a * τ e = τ.sesqForm G a a)
    (v w : n → A) :
    τ.sesqForm G (v ᵥ* lineMatrix τ G a e) (w ᵥ* lineMatrix τ G a e) = τ.sesqForm G v w := by
  have haw : τ.sesqForm G a w = -τ (τ.sesqForm G w a) := hG.sesqForm_swap τ w a
  have hkey := lineParameter_identity hc (map_sesqForm_self_eq_neg hG a) he
  rw [vecMul_lineMatrix, vecMul_lineMatrix, sesqForm_add_left, sesqForm_add_right,
    sesqForm_add_right, sesqForm_smul_left, sesqForm_smul_left, sesqForm_smul_right,
    sesqForm_smul_right, haw, map_mul]
  set c := τ.sesqForm G a a
  set k := c⁻¹ * (e - 1)
  set β := τ.sesqForm G v a
  set γ := τ.sesqForm G w a
  calc τ.sesqForm G v w + β * (τ k * τ γ) + (β * k * -τ γ + β * k * (c * (τ k * τ γ)))
      = τ.sesqForm G v w + β * (τ k - k + k * c * τ k) * τ γ := by noncomm_ring
    _ = τ.sesqForm G v w := by rw [hkey, mul_zero, zero_mul, add_zero]

/-- A form-preserving matrix satisfies the Gram matrix identity. -/
theorem mul_mul_matrix_eq_of_sesqForm (M : Matrix n n A)
    (h : ∀ v w, τ.sesqForm G (v ᵥ* M) (w ᵥ* M) = τ.sesqForm G v w) :
    M * G * τ.matrix n M = G := by
  ext i j
  rw [mul_mul_matrix_apply]
  have h' := h (Pi.single i 1) (Pi.single j 1)
  rw [single_one_vecMul, single_one_vecMul] at h'
  change τ.sesqForm G (M i) (M j) = _ at h'
  rw [h']
  simp [sesqForm, Pi.single_apply, apply_ite (⇑τ)]

/-- The unitary reflection: if `h(x, x) = h(y, y)` and `s = h(x, x - y)` is not fixed by `τ`,
the line matrix along `x - y` with parameter `τ(s) s⁻¹` sends `x` to `y`. -/
theorem reflection_spec (hG : τ.IsAntihermitian G) {x y : n → A}
    (hxy : τ.sesqForm G x x = τ.sesqForm G y y)
    (hs : τ (τ.sesqForm G x (x - y)) ≠ τ.sesqForm G x (x - y)) :
    τ.sesqForm G (x - y) (x - y) ≠ 0 ∧
      (τ (τ.sesqForm G x (x - y)) * (τ.sesqForm G x (x - y))⁻¹) *
          τ.sesqForm G (x - y) (x - y) *
          τ (τ (τ.sesqForm G x (x - y)) * (τ.sesqForm G x (x - y))⁻¹) =
        τ.sesqForm G (x - y) (x - y) ∧
      x ᵥ* lineMatrix τ G (x - y)
          (τ (τ.sesqForm G x (x - y)) * (τ.sesqForm G x (x - y))⁻¹) = y := by
  have hxx := map_sesqForm_self_eq_neg hG x
  have hyx : τ.sesqForm G y x = -τ (τ.sesqForm G x y) := hG.sesqForm_swap τ x y
  have hcs : τ.sesqForm G (x - y) (x - y) =
      τ.sesqForm G x (x - y) - τ (τ.sesqForm G x (x - y)) := by
    simp only [Eichler.sesqForm_sub_left, Eichler.sesqForm_sub_right, map_sub]
    rw [hxx, hyx, ← hxy]
    abel
  rw [vecMul_lineMatrix, hcs]
  set s := τ.sesqForm G x (x - y)
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    rw [h, map_zero]
  have hτs0 : τ s ≠ 0 := Eichler.map_ne_zero_of_ne_zero τ hs0
  have hc0 : s - τ s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  refine ⟨hc0, ?_, ?_⟩
  · rw [map_mul, Eichler.map_inv_eq, apply_apply]
    have h2 : τ s * (τ s)⁻¹ = 1 := mul_inv_cancel₀ hτs0
    have e1 : τ s * s⁻¹ * s = τ s := by rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    calc τ s * s⁻¹ * (s - τ s) * ((τ s)⁻¹ * s)
        = τ s * s⁻¹ * s * (τ s)⁻¹ * s - τ s * s⁻¹ * (τ s * (τ s)⁻¹) * s := by noncomm_ring
      _ = s - τ s := by rw [e1, h2, one_mul, mul_one, e1]
  · have hfac : τ s * s⁻¹ - 1 = -((s - τ s) * s⁻¹) := by
      rw [sub_mul, mul_inv_cancel₀ hs0]
      abel
    have hcoef : s * ((s - τ s)⁻¹ * (τ s * s⁻¹ - 1)) = -1 := by
      rw [hfac, mul_neg, inv_mul_cancel_left₀ hc0, mul_neg, mul_inv_cancel₀ hs0]
    rw [hcoef, neg_one_smul]
    abel

/-! ### Square roots of line parameters -/

section Roots

variable (τ) (N : A → K) (hN : ∀ x : A, x * τ x = algebraMap K A (N x))

include hN

theorem norm_algebraMap (t : K) : N (algebraMap K A t) = t * t := by
  apply (algebraMap K A).injective
  rw [← hN, τ.map_algebraMap, _root_.map_mul]

theorem norm_one : N 1 = 1 := by
  have h := norm_algebraMap τ N hN 1
  rw [_root_.map_one, mul_one] at h
  exact h

theorem map_mul_self (x : A) : τ x * x = algebraMap K A (N x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h := hN 0
    rw [zero_mul] at h
    rw [map_zero, zero_mul]
    exact h
  · have h := hN x
    have hτ : τ x = x⁻¹ * algebraMap K A (N x) := by
      rw [← h, inv_mul_cancel_left₀ hx]
    rw [hτ, mul_assoc, Algebra.commutes, inv_mul_cancel_left₀ hx]

theorem norm_map (x : A) : N (τ x) = N x := by
  apply (algebraMap K A).injective
  rw [← hN, apply_apply, map_mul_self τ N hN]

theorem norm_mul (x y : A) : N (x * y) = N x * N y := by
  apply (algebraMap K A).injective
  calc algebraMap K A (N (x * y)) = x * (y * τ y) * τ x := by
        rw [← hN, map_mul]; noncomm_ring
    _ = algebraMap K A (N y) * (x * τ x) := by
        rw [hN y, ← Algebra.commutes, mul_assoc]
    _ = algebraMap K A (N x * N y) := by rw [hN x, ← _root_.map_mul, mul_comm]

theorem norm_ne_zero {x : A} (hx : x ≠ 0) : N x ≠ 0 := by
  intro h
  have h' := hN x
  rw [h, _root_.map_zero] at h'
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact hx h1
  · exact Eichler.map_ne_zero_of_ne_zero τ hx h1

theorem add_map_eq (y : A) : y + τ y = algebraMap K A (N (1 + y) - 1 - N y) := by
  rw [_root_.map_sub, _root_.map_sub, _root_.map_one, ← hN, ← hN, map_add, map_one]
  noncomm_ring

theorem mem_range_of_map_eq [CharZero K] {y : A} (hy : τ y = y) :
    ∃ t : K, algebraMap K A t = y := by
  have h := add_map_eq τ N hN y
  rw [hy] at h
  refine ⟨(N (1 + y) - 1 - N y) / 2, ?_⟩
  have h2 : (2 : A) ≠ 0 := by
    rw [show (2 : A) = algebraMap K A 2 by rw [map_ofNat]]
    exact (_root_.map_ne_zero (algebraMap K A)).mpr two_ne_zero
  rw [div_eq_mul_inv, _root_.map_mul, ← h, map_inv₀, map_ofNat, ← mul_two, mul_assoc,
    mul_inv_cancel₀ h2, mul_one]

variable (hK1 : ∀ t : K, IsSquare t ∨ IsSquare (-t)) (hK2 : ∀ s t : K, IsSquare (s * s + t * t))

include hK1 hK2

/-- Suppose `x τ(x) = N(x)` is scalar-valued on the division algebra `A`. If `K` has
characteristic zero, every element or its negative is a square, and sums of two squares
are squares, then every value `N(y)` is a square in `K`. -/
theorem isSquare_norm [CharZero K] (y : A) : IsSquare (N y) := by
  rcases hK1 (N y) with h | ⟨w, hw⟩
  · exact h
  · have hNy : N y = -(w * w) := by rw [← hw, neg_neg]
    obtain ⟨β, hβ⟩ : ∃ β : K, algebraMap K A β = y + τ y := ⟨_, (add_map_eq τ N hN y).symm⟩
    obtain ⟨d, hd⟩ := hK2 β (2 * w)
    let t₀ : K := (d - β) / 2
    have ht₀ : t₀ * t₀ + β * t₀ + N y = 0 := by
      simp only [t₀, hNy]
      linear_combination (-1 / 4 : K) * hd
    have hc : y * algebraMap K A t₀ = algebraMap K A t₀ * y := (Algebra.commutes t₀ y).symm
    have hnorm : (algebraMap K A t₀ + y) * τ (algebraMap K A t₀ + y) = 0 := by
      calc (algebraMap K A t₀ + y) * τ (algebraMap K A t₀ + y)
          = algebraMap K A t₀ * algebraMap K A t₀ + algebraMap K A t₀ * (y + τ y) +
              y * τ y := by
            rw [map_add, τ.map_algebraMap, add_mul, mul_add, mul_add, hc]
            noncomm_ring
        _ = algebraMap K A (t₀ * t₀ + β * t₀ + N y) := by
            rw [← hβ, hN y, ← _root_.map_mul, ← _root_.map_mul, ← _root_.map_add,
              ← _root_.map_add, mul_comm t₀ β]
        _ = 0 := by rw [ht₀, _root_.map_zero]
    have hz : algebraMap K A t₀ + y = 0 := by
      rcases mul_eq_zero.mp hnorm with h | h
      · exact h
      · exact τ.injective (h.trans (map_zero τ).symm)
    have hy : y = algebraMap K A (-t₀) := by
      rw [_root_.map_neg]
      exact eq_neg_of_add_eq_zero_right hz
    rw [hy, norm_algebraMap τ N hN]
    exact ⟨-t₀, rfl⟩

variable (hK3 : ¬ IsSquare (-1 : K))

include hK3

/-- Assume the scalar norm and field hypotheses of `isSquare_norm`, and suppose `-1` is
nonsquare in `K`. If `c ≠ 0` is skew and `e c τ(e) = c`, then `e = f²` for a parameter `f`
with `f c τ(f) = c`. -/
theorem exists_sqrt_parameter [CharZero K] {c e : A} (hc : c ≠ 0) (hτc : τ c = -c)
    (he : e * c * τ e = c) : ∃ f : A, f * c * τ f = c ∧ f * f = e := by
  have hNc := norm_ne_zero τ N hN hc
  have hNe : N e = 1 := by
    have h := congrArg N he
    rw [norm_mul τ N hN, norm_mul τ N hN, norm_map τ N hN] at h
    have h1 : N e * N e = 1 := by
      have : (N e * N e - 1) * N c = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · linear_combination h'
      · exact absurd h' hNc
    rcases mul_self_eq_one_iff.mp h1 with h' | h'
    · exact h'
    · exact absurd (h' ▸ isSquare_norm τ N hN hK1 hK2 e) hK3
  have heτ : e * τ e = 1 := by rw [hN, hNe, _root_.map_one]
  have hτe : τ e * e = 1 := by rw [map_mul_self τ N hN, hNe, _root_.map_one]
  have hce : e * c = c * e := by
    calc e * c = e * c * (τ e * e) := by rw [hτe, mul_one]
      _ = c * e := by rw [← mul_assoc, he]
  have hcτe : c * τ e = τ e * c := by
    have h := congrArg τ hce
    rw [map_mul, map_mul, hτc, neg_mul, mul_neg, neg_inj] at h
    exact h
  by_cases h1e : 1 + e = 0
  · obtain ⟨r, hr⟩ := isSquare_norm τ N hN hK1 hK2 c
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hNc (by rw [hr, mul_zero])
    have hcc : c * c = -((r * r) • (1 : A)) := by
      rw [← hr, ← Algebra.algebraMap_eq_smul_one, ← hN, hτc, mul_neg, neg_neg]
    have hcτ : c * c * τ c = (r * r) • c := by
      rw [mul_assoc, hN c, hr, Algebra.smul_def, Algebra.commutes]
    have he1 : e = -1 := eq_neg_of_add_eq_zero_right h1e
    have hrr : r⁻¹ * r⁻¹ * (r * r) = 1 := by field_simp
    refine ⟨r⁻¹ • c, ?_, ?_⟩
    · calc (r⁻¹ • c) * c * τ (r⁻¹ • c) = (r⁻¹ * r⁻¹) • (c * c * τ c) := by
            rw [map_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
        _ = c := by rw [hcτ, smul_smul, hrr, one_smul]
    · calc (r⁻¹ • c) * (r⁻¹ • c) = (r⁻¹ * r⁻¹) • (c * c) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        _ = e := by rw [hcc, smul_neg, smul_smul, hrr, one_smul, he1]
  · set u := 1 + e with hu
    obtain ⟨r, hr⟩ := isSquare_norm τ N hN hK1 hK2 u
    have hNu := norm_ne_zero τ N hN h1e
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hNu (by rw [hr, mul_zero])
    have hrr : r⁻¹ * r⁻¹ * (r * r) = 1 := by field_simp
    have huu : u * u = (r * r) • e := by
      rw [← hr, Algebra.smul_def, ← hN, hu, map_add, map_one]
      calc (1 + e) * (1 + e) = (1 + e) * (e + τ e * e) := by rw [hτe]; noncomm_ring
        _ = (1 + e) * (1 + τ e) * e := by noncomm_ring
    have hcτ1 : c * (1 + τ e) = (1 + τ e) * c := by
      rw [mul_add, add_mul, mul_one, one_mul, hcτe]
    have huc : u * c * τ u = (r * r) • c := by
      rw [← hr, Algebra.smul_def, ← hN, hu, map_add, map_one]
      calc (1 + e) * c * (1 + τ e) = (1 + e) * (c * (1 + τ e)) := by noncomm_ring
        _ = (1 + e) * ((1 + τ e) * c) := by rw [hcτ1]
        _ = (1 + e) * (1 + τ e) * c := by noncomm_ring
    refine ⟨r⁻¹ • u, ?_, ?_⟩
    · calc (r⁻¹ • u) * c * τ (r⁻¹ • u) = (r⁻¹ * r⁻¹) • (u * c * τ u) := by
            rw [map_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
        _ = c := by rw [huc, smul_smul, hrr, one_smul]
    · calc (r⁻¹ • u) * (r⁻¹ • u) = (r⁻¹ * r⁻¹) • (u * u) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        _ = e := by rw [huu, smul_smul, hrr, one_smul]

end Roots

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution.LineRotation
