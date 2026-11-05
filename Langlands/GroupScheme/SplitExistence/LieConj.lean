import Langlands.GroupScheme.SplitExistence.LieRootData

/-! # Conjugating root operators by root exponentials

Over a commutative `ℚ`-algebra `R`, let `h : X →+ ℤ` be positive on the roots `k` and `η`. The
coefficients `σ_m(E_η)` of `x_k(g) E_η x_k(-g)` satisfy `σ_m(E_η) = 0` or
`σ_m(E_η) = q • E_θ` with `root θ = root η + m • root k`, by induction on `m` from the
recursion `(m + 1) σ_{m+1} = [E_k, σ_m]` and the integral bracket relation. Hence
`x_k(g) E_η x_k(-g) - E_η` lies in the `R`-span of the `E_θ` with
`root θ = root η + m • root k`, `m ≥ 1`, and the span of the `E_θ` for `θ` in a set `T` that
is closed under adding positive multiples of `root k` is stable under conjugation by `x_k(g)`. -/

noncomputable section

universe u

open Matrix Finset

namespace Langlands.GroupScheme.SplitExistence

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]

namespace LieRootData

variable {P : RootDatum J X Y} (D : LieRootData P)

variable (R : Type*) [CommRing R]

/-- The `R`-span of the root operators `E_θ`, `θ ∈ T`. -/
def V (T : Set J) : Submodule R (Matrix (Fin D.n) (Fin D.n) R) :=
  Submodule.span R (D.E R '' T)

variable {R}

theorem E_mem_V {T : Set J} {θ : J} (hθ : θ ∈ T) : D.E R θ ∈ D.V R T :=
  Submodule.subset_span ⟨θ, hθ, rfl⟩

theorem V_mono {T T' : Set J} (h : T ⊆ T') : D.V R T ≤ D.V R T' :=
  Submodule.span_mono (Set.image_mono h)

/-- The integral bracket relation over `R`. -/
theorem lie_E_E (j j' : J) (h : P.root j' ≠ -P.root j) :
    D.E R j * D.E R j' - D.E R j' * D.E R j = 0 ∨
      ∃ (k : J) (c : ℤ), P.root k = P.root j + P.root j' ∧
        D.E R j * D.E R j' - D.E R j' * D.E R j = (c : R) • D.E R k := by
  have hmap : D.E R j * D.E R j' - D.E R j' * D.E R j =
      (Int.castRingHom R).mapMatrix (D.e j 1 * D.e j' 1 - D.e j' 1 * D.e j 1) := by
    simp only [map_sub, map_mul]
    rfl
  rcases D.lie_e_e j j' h with h0 | ⟨k, c, hk, hc⟩
  · left
    rw [hmap, h0, map_zero]
  · right
    refine ⟨k, c, hk, ?_⟩
    rw [hmap, hc]
    ext x y
    simp only [E, em, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      eq_intCast, Int.cast_mul]

/-- Iterated brackets: `σ_m(E_η)` is zero or a multiple of a single root operator `E_θ` with
`root θ = root η + m • root k`. -/
theorem sigma_E [Algebra ℚ R] (h : X →+ ℤ) {k η : J} (hk : 0 < h (P.root k))
    (hη : 0 < h (P.root η)) (m : ℕ) :
    D.sigma R k m (D.E R η) = 0 ∨
      ∃ (θ : J) (q : R), P.root θ = P.root η + m • P.root k ∧
        D.sigma R k m (D.E R η) = q • D.E R θ := by
  induction m with
  | zero => exact Or.inr ⟨η, 1, by simp, by rw [D.sigma_zero, one_smul]⟩
  | succ m ih =>
    set u : R := algebraMap ℚ R ((m + 1 : ℕ) : ℚ)⁻¹ with hu
    have hu1 : u * ((m + 1 : ℕ) : R) = 1 := by
      rw [hu, ← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ (by positivity),
        map_one]
    have hsig : D.sigma R k (m + 1) (D.E R η) =
        u • (D.E R k * D.sigma R k m (D.E R η) - D.sigma R k m (D.E R η) * D.E R k) := by
      rw [← D.sigma_succ (R := R), smul_smul, hu1, one_smul]
    rcases ih with h0 | ⟨θ, q, hθ, hq⟩
    · left
      rw [hsig, h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero, smul_zero]
    · have hθk : P.root θ ≠ -P.root k := by
        intro hc
        have h1 := congrArg h hc
        rw [hθ, map_add, map_nsmul, map_neg] at h1
        have : (0 : ℤ) ≤ m • h (P.root k) := nsmul_nonneg hk.le m
        linarith
      have hcomm : D.E R k * D.sigma R k m (D.E R η) - D.sigma R k m (D.E R η) * D.E R k =
          q • (D.E R k * D.E R θ - D.E R θ * D.E R k) := by
        rw [hq, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      rcases D.lie_E_E (R := R) k θ hθk with h0 | ⟨κ, c, hκ, hc⟩
      · left
        rw [hsig, hcomm, h0, smul_zero, smul_zero]
      · right
        refine ⟨κ, u * q * c, ?_, ?_⟩
        · rw [hκ, hθ, succ_nsmul]
          abel
        · rw [hsig, hcomm, hc, smul_smul, smul_smul]

/-- `x_k(g) E_η x_k(-g) - E_η` lies in the span of the `E_θ` with
`root θ = root η + m • root k`, `m ≥ 1`. -/
theorem conj_sub_mem [Algebra ℚ R] (h : X →+ ℤ) {k η : J} (hk : 0 < h (P.root k))
    (hη : 0 < h (P.root η)) (g : R) :
    divExp (D.e k) g * D.E R η * divExp (D.e k) (-g) - D.E R η ∈
      D.V R {θ | ∃ m : ℕ, 1 ≤ m ∧ P.root θ = P.root η + m • P.root k} := by
  rw [D.conj_eq_sum, Finset.sum_range_succ', pow_zero, one_smul, D.sigma_zero,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  rcases D.sigma_E (R := R) h hk hη (m + 1) with h0 | ⟨θ, q, hθ, hq⟩
  · rw [h0]
    exact Submodule.zero_mem _
  · rw [hq]
    exact Submodule.smul_mem _ _ (D.E_mem_V ⟨m + 1, by omega, hθ⟩)

/-- The span of the `E_θ`, `θ ∈ T`, is stable under conjugation by `x_k(g)` when `T` is closed
under adding positive multiples of `root k` (and `h` is positive on `k` and on `T`). -/
theorem conj_mem [Algebra ℚ R] (h : X →+ ℤ) {k : J} {T : Set J} (hk : 0 < h (P.root k))
    (hT : ∀ θ ∈ T, 0 < h (P.root θ))
    (hcl : ∀ θ ∈ T, ∀ m : ℕ, 1 ≤ m → ∀ κ, P.root κ = P.root θ + m • P.root k → κ ∈ T)
    (g : R) {B : Matrix (Fin D.n) (Fin D.n) R} (hB : B ∈ D.V R T) :
    divExp (D.e k) g * B * divExp (D.e k) (-g) ∈ D.V R T := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨θ, hθ, rfl⟩ := hB
    have h1 := D.conj_sub_mem h hk (hT θ hθ) g
    have h2 : D.V R {κ | ∃ m : ℕ, 1 ≤ m ∧ P.root κ = P.root θ + m • P.root k} ≤ D.V R T :=
      D.V_mono fun κ ⟨m, hm, hκ⟩ => hcl θ hθ m hm κ hκ
    rw [← sub_add_cancel (divExp (D.e k) g * D.E R θ * divExp (D.e k) (-g)) (D.E R θ)]
    exact Submodule.add_mem _ (h2 h1) (D.E_mem_V hθ)
  | zero => simp
  | add B B' _ _ hB hB' =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ hB hB'
  | smul a B _ hB =>
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem _ _ hB

end LieRootData

end Langlands.GroupScheme.SplitExistence
