import Mathlib.RingTheory.Valuation.Integers
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Basis

/-!
# Conjugates of the integral general linear group over a valued field

For a field `F` with a valuation `v` and `K = GL_N(𝒪)`, `𝒪 = v.integer`:

* `isIntegral_inv_mul_mul_of_conj`: if `k K k⁻¹ ⊆ K` then `k⁻¹ K k ⊆ K`, so `k K k⁻¹ = K`;
* `exists_diagonal_conj_bound`: for `A ∈ GL_N(F)` there are units `l₁, …, l_N` such that every
  `g ∈ A K A⁻¹` for which each column of `g - 1` has at most one nonzero entry satisfies
  `v(l_i⁻¹ g_{ij} l_j) ≤ 1` for all `i, j`, i.e. `g` lies in `t K t⁻¹` for `t = diag(l)`.

The second statement is the matrix form of the lattice argument: `l_j e_j` spans the
intersection of the lattice `A 𝒪^N` with the line `F e_j`.
-/

noncomputable section

open Matrix

namespace Langlands.BruhatTits.Cartan.GeneralLinearRecovery

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀) {N : ℕ}

/-- Every entry of `M` has valuation at most `r`. -/
def EntryBounded (M : Matrix (Fin N) (Fin N) F) (r : Γ₀) : Prop :=
  ∀ i j, v (M i j) ≤ r

/-- `g` and `g⁻¹` have integral entries: `g ∈ GL_N(𝒪)`. -/
def IsIntegral (g : GL (Fin N) F) : Prop :=
  EntryBounded v (g : Matrix (Fin N) (Fin N) F) 1 ∧
    EntryBounded v ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) 1

variable {v}

theorem EntryBounded.mul {M M' : Matrix (Fin N) (Fin N) F} {r r' : Γ₀}
    (h : EntryBounded v M r) (h' : EntryBounded v M' r') :
    EntryBounded v (M * M') (r * r') := by
  intro i j
  rw [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro k _
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

theorem EntryBounded.sub {M M' : Matrix (Fin N) (Fin N) F} {r : Γ₀}
    (h : EntryBounded v M r) (h' : EntryBounded v M' r) :
    EntryBounded v (M - M') r := by
  intro i j
  rw [Matrix.sub_apply]
  exact (Valuation.map_sub v _ _).trans (max_le (h i j) (h' i j))

theorem EntryBounded.add {M M' : Matrix (Fin N) (Fin N) F} {r : Γ₀}
    (h : EntryBounded v M r) (h' : EntryBounded v M' r) :
    EntryBounded v (M + M') r := by
  intro i j
  rw [Matrix.add_apply]
  exact (Valuation.map_add v _ _).trans (max_le (h i j) (h' i j))

theorem entryBounded_one : EntryBounded v (1 : Matrix (Fin N) (Fin N) F) 1 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]
    exact zero_le

theorem entryBounded_single (i j : Fin N) :
    EntryBounded v (Matrix.single i j (1 : F)) 1 := by
  intro p q
  rw [Matrix.single_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]
    exact zero_le

theorem mul_single_mul_apply (k k' : Matrix (Fin N) (Fin N) F) (i j p q : Fin N) :
    (k * Matrix.single i j (1 : F) * k') p q = k p i * k' j q := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.single_apply]
  simp [ite_and]

/-- `GL_N(𝒪)` inside `GL_N(F)`: the image of `GL_N(v.integer)` consists exactly of the matrices
`g` such that `g` and `g⁻¹` have integral entries. -/
theorem mem_range_map_iff (g : GL (Fin N) F) :
    g ∈ (Matrix.GeneralLinearGroup.map (algebraMap v.integer F)).range ↔ IsIntegral v g := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact (h.val i j).property
    · rw [← Matrix.GeneralLinearGroup.map_inv]
      exact (h⁻¹.val i j).property
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin N) (Fin N) v.integer :=
      Matrix.of fun i j => ⟨(g : Matrix (Fin N) (Fin N) F) i j, h1 i j⟩
    let B : Matrix (Fin N) (Fin N) v.integer :=
      Matrix.of fun i j => ⟨((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) i j, h2 i j⟩
    have hA : A.map (algebraMap v.integer F) = (g : Matrix (Fin N) (Fin N) F) := by
      ext i j
      rfl
    have hB : B.map (algebraMap v.integer F) =
        ((g⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by
      ext i j
      rfl
    have hinj : Function.Injective
        (fun M : Matrix (Fin N) (Fin N) v.integer => M.map (algebraMap v.integer F)) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := by
      apply hinj
      simp only
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    have hBA : B * A = 1 := by
      apply hinj
      simp only
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
        inv_mul_cancel, Units.val_one]
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    apply Units.ext
    exact hA

/-! ### `k K k⁻¹ ⊆ K` forces `k ∈ F^× K` -/

theorem conj_single_bounded {k : GL (Fin N) F}
    (hk : ∀ g : GL (Fin N) F, IsIntegral v g → IsIntegral v (k * g * k⁻¹)) (i j : Fin N) :
    EntryBounded v ((k : Matrix (Fin N) (Fin N) F) * Matrix.single i j 1 *
      ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) 1 := by
  have hkk : (k : Matrix (Fin N) (Fin N) F) *
      ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hkk' : ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) *
      (k : Matrix (Fin N) (Fin N) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- the off-diagonal case
  have hoff : ∀ a b : Fin N, a ≠ b →
      EntryBounded v ((k : Matrix (Fin N) (Fin N) F) * Matrix.single a b 1 *
        ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) 1 := by
    intro a b hab
    have hsq : Matrix.single a b (1 : F) * Matrix.single a b 1 = 0 := by
      simp [Ne.symm hab]
    let T : GL (Fin N) F :=
      ⟨1 + Matrix.single a b 1, 1 - Matrix.single a b 1,
        by rw [add_mul, one_mul, mul_sub, mul_one, hsq, sub_zero, sub_add_cancel],
        by rw [sub_mul, one_mul, mul_add, mul_one, hsq, add_zero, add_sub_cancel_right]⟩
    have hT : IsIntegral v T :=
      ⟨entryBounded_one.add (entryBounded_single a b),
        entryBounded_one.sub (entryBounded_single a b)⟩
    have h := (hk T hT).1
    have heq : (k : Matrix (Fin N) (Fin N) F) * Matrix.single a b 1 *
        ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) =
        ((k * T * k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) - 1 := by
      rw [Units.val_mul, Units.val_mul]
      change _ = (k : Matrix (Fin N) (Fin N) F) * (1 + Matrix.single a b 1) * _ - 1
      rw [mul_add, mul_one, add_mul, hkk, add_sub_cancel_left]
    rw [heq]
    exact h.sub entryBounded_one
  by_cases hij : i = j
  · subst hij
    by_cases hm : ∃ m : Fin N, m ≠ i
    · obtain ⟨m, hm⟩ := hm
      have hprod : (k : Matrix (Fin N) (Fin N) F) * Matrix.single i i 1 *
          ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) =
          ((k : Matrix (Fin N) (Fin N) F) * Matrix.single i m 1 *
            ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) *
          ((k : Matrix (Fin N) (Fin N) F) * Matrix.single m i 1 *
            ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) := by
        rw [show ((k : Matrix (Fin N) (Fin N) F) * Matrix.single i m 1 *
            ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) *
          ((k : Matrix (Fin N) (Fin N) F) * Matrix.single m i 1 *
            ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) =
          (k : Matrix (Fin N) (Fin N) F) * (Matrix.single i m 1 *
            (((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) *
              (k : Matrix (Fin N) (Fin N) F)) * Matrix.single m i 1) *
            ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) by
          simp only [Matrix.mul_assoc]]
        rw [hkk', Matrix.mul_one, Matrix.single_mul_single_same, mul_one]
      rw [hprod, ← mul_one (1 : Γ₀)]
      exact (hoff i m (Ne.symm hm)).mul (hoff m i hm)
    · push Not at hm
      have hone : Matrix.single i i (1 : F) = 1 := by
        ext p q
        rw [hm p, hm q, Matrix.single_apply_same, Matrix.one_apply_eq]
      rw [hone, Matrix.mul_one, hkk]
      exact entryBounded_one
  · exact hoff i j hij

theorem exists_scalar_of_conj {k : GL (Fin N) F}
    (hk : ∀ g : GL (Fin N) F, IsIntegral v g → IsIntegral v (k * g * k⁻¹)) :
    ∃ c : F, c ≠ 0 ∧ (∀ p i, v ((k : Matrix (Fin N) (Fin N) F) p i) ≤ v c) ∧
      ∀ j q, v (c * ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) j q) ≤ 1 := by
  have hprod : ∀ p i j q, v ((k : Matrix (Fin N) (Fin N) F) p i *
      ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) j q) ≤ 1 := by
    intro p i j q
    have h := conj_single_bounded hk i j p q
    rwa [mul_single_mul_apply] at h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨1, one_ne_zero, fun p => p.elim0, fun j => j.elim0⟩
  · obtain ⟨x, -, hx⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
      (fun x => v ((k : Matrix (Fin N) (Fin N) F) x.1 x.2))
      ⟨(⟨0, hN⟩, ⟨0, hN⟩), Finset.mem_univ _⟩
    have hc : (k : Matrix (Fin N) (Fin N) F) x.1 x.2 ≠ 0 := by
      intro h0
      have hzero : (k : Matrix (Fin N) (Fin N) F) = 0 := by
        ext p i
        have h := hx (p, i) (Finset.mem_univ _)
        simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h
        exact h
      have h1 := congrArg (fun M : Matrix (Fin N) (Fin N) F => M ⟨0, hN⟩ ⟨0, hN⟩)
        (show (k : Matrix (Fin N) (Fin N) F) *
            ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = 1 by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      simp [hzero] at h1
    refine ⟨(k : Matrix (Fin N) (Fin N) F) x.1 x.2, hc,
      fun p i => hx (p, i) (Finset.mem_univ _), fun j q => ?_⟩
    rw [map_mul]
    rw [← map_mul]
    exact hprod x.1 x.2 j q

/-- **`k K k⁻¹ ⊆ K` implies `k⁻¹ K k ⊆ K`** for `K = GL_N(𝒪)`. -/
theorem isIntegral_inv_mul_mul_of_conj {k : GL (Fin N) F}
    (hk : ∀ g : GL (Fin N) F, IsIntegral v g → IsIntegral v (k * g * k⁻¹))
    (g : GL (Fin N) F) (hg : IsIntegral v g) : IsIntegral v (k⁻¹ * g * k) := by
  obtain ⟨c, hc, hk1, hk2⟩ := exists_scalar_of_conj hk
  have hA : EntryBounded v (c • ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) 1 := by
    intro j q
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hk2 j q
  have hB : EntryBounded v (c⁻¹ • (k : Matrix (Fin N) (Fin N) F)) 1 := by
    intro p i
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hvc : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
    calc (v c)⁻¹ * v ((k : Matrix (Fin N) (Fin N) F) p i) ≤ (v c)⁻¹ * v c :=
          mul_le_mul_right (hk1 p i) _
      _ = 1 := inv_mul_cancel₀ hvc
  have hconj : ∀ h : GL (Fin N) F,
      ((k⁻¹ * h * k : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) =
        (c • ((k⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) *
          (h : Matrix (Fin N) (Fin N) F) * (c⁻¹ • (k : Matrix (Fin N) (Fin N) F)) := by
    intro h
    rw [Units.val_mul, Units.val_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc, one_smul]
  refine ⟨?_, ?_⟩
  · rw [hconj g, ← mul_one (1 : Γ₀), ← mul_one ((1 : Γ₀) * 1)]
    exact (hA.mul hg.1).mul hB
  · rw [show (k⁻¹ * g * k)⁻¹ = k⁻¹ * g⁻¹ * k by group, hconj g⁻¹,
      ← mul_one (1 : Γ₀), ← mul_one ((1 : Γ₀) * 1)]
    exact (hA.mul hg.2).mul hB

/-! ### Adapting a conjugate of `K` to the diagonal torus -/

/-- Each column of `M - 1` has at most one nonzero entry. -/
def ColumnSupported (M : Matrix (Fin N) (Fin N) F) : Prop :=
  ∀ i i' j, (M - 1) i j ≠ 0 → (M - 1) i' j ≠ 0 → i = i'

/-- The matrix core of `exists_diagonal_conj_bound`: `B = A⁻¹`, and `p k` is a row index of
maximal valuation in column `k` of `B`. -/
theorem diagonal_conj_bound_aux (A B : Matrix (Fin N) (Fin N) F) (hAB : A * B = 1)
    (p : Fin N → Fin N) (hp : ∀ k p', v (B p' k) ≤ v (B (p k) k)) (hμ : ∀ k, B (p k) k ≠ 0)
    (g : Matrix (Fin N) (Fin N) F) (hg : EntryBounded v (B * g * A) 1)
    (hcol : ColumnSupported g) (i j : Fin N) :
    v (B (p i) i * g i j * (B (p j) j)⁻¹) ≤ 1 := by
  let T : Matrix (Fin N) (Fin N) F := Matrix.diagonal fun k => (B (p k) k)⁻¹
  -- `B T` has integral entries
  have hBT : EntryBounded v (B * T) 1 := by
    intro r k
    rw [Matrix.mul_diagonal]
    have hv : v (B (p k) k) ≠ 0 := (Valuation.ne_zero_iff v).mpr (hμ k)
    rw [map_mul, map_inv₀]
    calc v (B r k) * (v (B (p k) k))⁻¹ ≤ v (B (p k) k) * (v (B (p k) k))⁻¹ :=
          mul_le_mul_left (hp k r) _
      _ = 1 := mul_inv_cancel₀ hv
  -- `B (g - 1) T = (B g A)(B T) - B T` has integral entries
  have hM : EntryBounded v (B * (g - 1) * T) 1 := by
    have heq : B * (g - 1) * T = (B * g * A) * (B * T) - B * T := by
      rw [show B * g * A * (B * T) = B * g * (A * B) * T by simp only [Matrix.mul_assoc]]
      rw [hAB, Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [heq]
    have h1 : EntryBounded v ((B * g * A) * (B * T)) 1 := by
      rw [← mul_one (1 : Γ₀)]
      exact hg.mul hBT
    exact h1.sub hBT
  have hδ : B (p i) i * (1 : Matrix (Fin N) (Fin N) F) i j * (B (p j) j)⁻¹ =
      (1 : Matrix (Fin N) (Fin N) F) i j := by
    rw [Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [mul_one, mul_inv_cancel₀ (hμ i)]
    · rw [mul_zero, zero_mul]
  have hentry : B (p i) i * g i j * (B (p j) j)⁻¹ =
      (1 : Matrix (Fin N) (Fin N) F) i j + B (p i) i * (g - 1) i j * (B (p j) j)⁻¹ := by
    rw [Matrix.sub_apply, mul_sub, sub_mul, hδ]
    ring
  rw [hentry]
  refine (Valuation.map_add v _ _).trans (max_le (entryBounded_one i j) ?_)
  by_cases hij : (g - 1) i j = 0
  · rw [hij, mul_zero, zero_mul, map_zero]
    exact zero_le
  · have h := hM (p i) j
    have hsum : (B * (g - 1) * T) (p i) j = B (p i) i * (g - 1) i j * (B (p j) j)⁻¹ := by
      rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single i]
      · intro r _ hr
        by_cases hr0 : (g - 1) r j = 0
        · rw [hr0, mul_zero]
        · exact absurd (hcol r i j hr0 hij) hr
      · intro h
        exact absurd (Finset.mem_univ i) h
    rwa [hsum] at h

/-- **The diagonal element adapted to a conjugate of `K`.** For `A ∈ GL_N(F)` there are units
`l_j` (with `l_j e_j` spanning the intersection of `A 𝒪^N` with `F e_j`) such that every `g` with
`A⁻¹ g A` integral whose columns of `g - 1` have at most one nonzero entry satisfies
`v(l_i⁻¹ g_{ij} l_j) ≤ 1`. -/
theorem exists_diagonal_conj_bound (A : GL (Fin N) F) :
    ∃ l : Fin N → Fˣ, ∀ g : GL (Fin N) F,
      EntryBounded v ((A⁻¹ * g * A : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) 1 →
        ColumnSupported (g : Matrix (Fin N) (Fin N) F) →
          ∀ i j, v (((l i)⁻¹ : Fˣ) * (g : Matrix (Fin N) (Fin N) F) i j * (l j : F)) ≤ 1 := by
  classical
  have hAB : (A : Matrix (Fin N) (Fin N) F) *
      ((A⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- a row index of maximal valuation in every column of `A⁻¹`
  have hmax : ∀ k : Fin N, ∃ p : Fin N, ∀ p',
      v (((A⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p' k) ≤
        v (((A⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p k) := by
    intro k
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N))
      (fun p => v (((A⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p k)) ⟨k, Finset.mem_univ _⟩
    exact ⟨p, fun p' => hp p' (Finset.mem_univ _)⟩
  choose p hp using hmax
  have hμ : ∀ k, ((A⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) (p k) k ≠ 0 := by
    intro k h0
    have hcol : ∀ r, ((A⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) r k = 0 := by
      intro r
      have h := hp k r
      rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h
      exact h
    have h1 := congrArg (fun M : Matrix (Fin N) (Fin N) F => M k k) hAB
    simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  refine ⟨fun k => (Units.mk0 _ (hμ k))⁻¹, ?_⟩
  intro g hg hcol i j
  rw [inv_inv, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  rw [Units.val_mul, Units.val_mul] at hg
  exact diagonal_conj_bound_aux _ _ hAB p hp hμ _ hg hcol i j

end Langlands.BruhatTits.Cartan.GeneralLinearRecovery
