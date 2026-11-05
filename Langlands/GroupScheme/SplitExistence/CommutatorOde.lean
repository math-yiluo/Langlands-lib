import Langlands.GroupScheme.SplitExistence.OdePeel

/-! # The commutator of two root exponentials over a polynomial ring

Let `A` be a torsion-free commutative `ℚ`-algebra, `t ∈ A`, and let `h : X →+ ℤ` be positive
on the roots `γ` and `δ`. Over `A[X]` the group commutator
`c = x_γ(X) x_δ(t) x_γ(-X) x_δ(-t)` satisfies `c' = M c` with
`M = -x_γ(X) (x_δ(t) E_γ x_δ(-t) - E_γ) x_γ(-X)`, and `M` lies in the span of the root
operators `E_θ` with `root θ = a • root γ + c • root δ`, `a, c ≥ 1`. Since `c(0) = 1`, ODE
peeling writes `c` as an ordered product of root exponentials of such roots. -/

noncomputable section

universe u

open Matrix Finset Polynomial

namespace Langlands.GroupScheme.SplitExistence

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]

/-- The roots `θ` with `root θ = a • root γ + c • root δ` for some `a, c ≥ 1`. -/
def commRoots (P : RootDatum J X Y) (γ δ : J) : Set J :=
  {θ | ∃ a c : ℕ, 1 ≤ a ∧ 1 ≤ c ∧ P.root θ = a • P.root γ + c • P.root δ}

variable {P : RootDatum J X Y}

theorem commRoots_pos (h : X →+ ℤ) {γ δ : J} (hγ : 0 < h (P.root γ)) (hδ : 0 < h (P.root δ))
    {θ : J} (hθ : θ ∈ commRoots P γ δ) : 0 < h (P.root θ) := by
  obtain ⟨a, c, ha, hc, hθ⟩ := hθ
  rw [hθ, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
  nlinarith

theorem commRoots_closed {γ δ a b : J} (ha : a ∈ commRoots P γ δ) (hb : b ∈ commRoots P γ δ)
    (m : ℕ) {θ : J} (hθ : P.root θ = P.root a + m • P.root b) : θ ∈ commRoots P γ δ := by
  obtain ⟨a₁, c₁, ha₁, hc₁, ha⟩ := ha
  obtain ⟨a₂, c₂, -, -, hb⟩ := hb
  refine ⟨a₁ + m * a₂, c₁ + m * c₂, by omega, by omega, ?_⟩
  rw [hθ, ha, hb, smul_add, smul_smul, smul_smul, add_smul, add_smul]
  abel

theorem commRoots_add {γ δ θ : J} (hθ : θ ∈ commRoots P γ δ) (m : ℕ) {κ : J}
    (hκ : P.root κ = P.root θ + m • P.root γ) : κ ∈ commRoots P γ δ := by
  obtain ⟨a, c, ha, hc, hθ⟩ := hθ
  refine ⟨a + m, c, by omega, hc, ?_⟩
  rw [hκ, hθ, add_smul]
  abel

theorem subset_commRoots {γ δ : J} :
    {θ | ∃ m : ℕ, 1 ≤ m ∧ P.root θ = P.root γ + m • P.root δ} ⊆ commRoots P γ δ := by
  rintro θ ⟨m, hm, hθ⟩
  exact ⟨1, m, le_rfl, hm, by rw [hθ, one_smul]⟩

/-- A ring identity behind the commutator ODE. -/
theorem commutator_ode_aux {R : Type*} [Ring R] (a b a' b' E : R) (h1 : a' * a = 1)
    (h2 : b' * b = 1) (h3 : E * a = a * E) :
    -(a * (b * E * b' - E) * a') * (a * b * a' * b') = E * (a * b * a' * b') - a * b * E * a' * b' := by
  have key : (a * (b * E * b' - E) * a') * (a * b * a' * b') =
      a * b * E * a' * b' - E * (a * b * a' * b') :=
    calc (a * (b * E * b' - E) * a') * (a * b * a' * b')
        = a * (b * E * b' - E) * (a' * a) * b * a' * b' := by simp only [mul_assoc]
      _ = a * (b * E * b' - E) * b * a' * b' := by rw [h1, mul_one]
      _ = a * b * E * (b' * b) * a' * b' - a * E * b * a' * b' := by
          simp only [mul_sub, sub_mul, mul_assoc]
      _ = a * b * E * a' * b' - E * (a * b * a' * b') := by
          rw [h2, mul_one, ← h3]
          simp only [mul_assoc]
  rw [neg_mul, key, neg_sub]

namespace LieRootData

variable (D : LieRootData P) {A : Type*} [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A]

/-- The commutator `x_γ(X) x_δ(t) x_γ(-X) x_δ(-t)` over `A[X]` is an ordered product of root
exponentials of roots `a • root γ + c • root δ` (`a, c ≥ 1`) with distinct roots and
nondecreasing `h`-values. -/
theorem exists_list_commutator_poly [Finite J] (h : X →+ ℤ) {γ δ : J}
    (hγ : 0 < h (P.root γ)) (hδ : 0 < h (P.root δ)) (t : A) :
    ∃ L : List (J × A[X]), (∀ p ∈ L, p.1 ∈ commRoots P γ δ) ∧
      L.Pairwise (fun p q => p.1 ≠ q.1 ∧ h (P.root p.1) ≤ h (P.root q.1)) ∧
      divExp (D.e γ) (Polynomial.X : A[X]) * divExp (D.e δ) (C t) * divExp (D.e γ) (-Polynomial.X) *
          divExp (D.e δ) (-C t) = (L.map fun p => divExp (D.e p.1) p.2).prod := by
  classical
  have := Fintype.ofFinite J
  set Ψ : Finset J := Finset.univ.filter (· ∈ commRoots P γ δ) with hΨdef
  have hΨ : ∀ θ, θ ∈ Ψ ↔ θ ∈ commRoots P γ δ := by
    intro θ
    simp [hΨdef]
  have hΨset : (Ψ : Set J) = commRoots P γ δ := by
    ext θ
    exact hΨ θ
  set a := divExp (D.e γ) (Polynomial.X : A[X]) with ha
  set b := divExp (D.e δ) (C t : A[X]) with hb
  set a' := divExp (D.e γ) (-Polynomial.X : A[X]) with ha'
  set b' := divExp (D.e δ) (-C t : A[X]) with hb'
  set E := D.E A[X] γ with hE
  set N := b * E * b' - E with hN
  have hNmem : N ∈ D.V A[X] (commRoots P γ δ) :=
    D.V_mono subset_commRoots (D.conj_sub_mem h hδ hγ (C t))
  have hMmem : -(a * N * a') ∈ D.V A[X] (Ψ : Set J) := by
    rw [hΨset]
    exact Submodule.neg_mem _ (D.conj_mem h hγ (fun θ hθ => commRoots_pos h hγ hδ hθ)
      (fun θ hθ m _ κ hκ => commRoots_add hθ m hκ) Polynomial.X hNmem)
  have hc : mderiv (a * b * a' * b') = -(a * N * a') * (a * b * a' * b') := by
    rw [hN, commutator_ode_aux a b a' b' E (D.divExp_neg_mul_divExp γ Polynomial.X)
      (D.divExp_neg_mul_divExp δ (C t)) (D.commute_E_divExp γ Polynomial.X).eq]
    rw [mderiv_mul, mderiv_mul, mderiv_mul, ha, hb, ha', hb', D.mderiv_divExp,
      D.mderiv_divExp, D.mderiv_divExp, D.mderiv_divExp]
    simp only [derivative_X, derivative_C, derivative_neg, neg_zero, one_smul, zero_smul,
      neg_smul, Matrix.mul_zero, add_zero, Matrix.mul_neg, ← sub_eq_add_neg, hE]
    simp only [sub_mul, mul_assoc]
  have h0 : (a * b * a' * b').map (evalRingHom 0) = 1 := by
    rw [ha, hb, ha', hb', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, divExp_map,
      divExp_map, divExp_map, divExp_map]
    simp only [coe_evalRingHom, eval_X, eval_C, eval_neg, neg_zero,
      divExp_zero (D.isDividedPowerFamily γ), Matrix.one_mul, Matrix.mul_one]
    exact D.divExp_mul_divExp_neg δ t
  obtain ⟨L, hL₁, hL₂, hL₃⟩ := D.ode_peel h Ψ
    (fun θ hθ => commRoots_pos h hγ hδ ((hΨ θ).mp hθ))
    (fun a₀ ha₀ b₀ hb₀ m _ θ hθ =>
      (hΨ θ).mpr (commRoots_closed ((hΨ a₀).mp ha₀) ((hΨ b₀).mp hb₀) m hθ))
    _ _ hMmem hc h0
  exact ⟨L, fun p hp => (hΨ p.1).mp (hL₁ p hp), hL₂, hL₃⟩

end LieRootData

end Langlands.GroupScheme.SplitExistence
