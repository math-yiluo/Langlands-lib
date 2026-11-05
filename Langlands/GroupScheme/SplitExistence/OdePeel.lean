import Langlands.GroupScheme.SplitExistence.MatDeriv

/-! # Solutions of root-operator ODEs are ordered products of root exponentials

Let `A` be a torsion-free commutative `ℚ`-algebra, let `h : X →+ ℤ`, and let `Ψ` be a finite
set of roots on which `h` is positive and which is closed under `(a, b) ↦ a + m • b` (`m ≥ 1`).
If a matrix `c` over `A[X]` satisfies `c' = M c` with `M` in the `A[X]`-span of the root
operators `E_θ`, `θ ∈ Ψ`, and `c(0) = 1`, then `c` is a product `x_{θ₁}(f₁) ⋯ x_{θ_r}(f_r)` of
root exponentials with distinct `θ_i ∈ Ψ` and `h(θ_1) ≤ ⋯ ≤ h(θ_r)`.

The proof peels off the `h`-minimal root `ε`: writing `M = m₀ E_ε + M₁` and `F` for the
antiderivative of `m₀` vanishing at `0`, the matrix `c₁ = x_ε(-F) c` satisfies
`c₁' = (x_ε(-F) M₁ x_ε(F)) c₁`, and conjugation by `x_ε(-F)` keeps `M₁` in the span of the
`E_θ` with `θ ∈ Ψ \ {ε}`. -/

noncomputable section

universe u

open Matrix Finset Polynomial

namespace Langlands.GroupScheme.SplitExistence

namespace LieRootData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}
  (D : LieRootData P) {R : Type*} [CommRing R]

theorem divExp_mul_divExp_neg (k : J) (f : R) :
    divExp (D.e k) f * divExp (D.e k) (-f) = 1 := by
  rw [divExp_mul (D.isDividedPowerFamily k), add_neg_cancel,
    divExp_zero (D.isDividedPowerFamily k)]

theorem divExp_neg_mul_divExp (k : J) (f : R) :
    divExp (D.e k) (-f) * divExp (D.e k) f = 1 := by
  rw [divExp_mul (D.isDividedPowerFamily k), neg_add_cancel,
    divExp_zero (D.isDividedPowerFamily k)]

variable {A : Type*} [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A]

/-- **ODE peeling.** A solution of `c' = M c`, `c(0) = 1`, with `M` in the span of the root
operators `E_θ`, `θ ∈ Ψ`, is an ordered product of root exponentials `x_θ(f)`, `θ ∈ Ψ`, with
distinct roots and nondecreasing `h`-values. -/
theorem ode_peel (h : X →+ ℤ) : ∀ (Ψ : Finset J), (∀ θ ∈ Ψ, 0 < h (P.root θ)) →
    (∀ a ∈ Ψ, ∀ b ∈ Ψ, ∀ m : ℕ, 1 ≤ m → ∀ θ, P.root θ = P.root a + m • P.root b → θ ∈ Ψ) →
    ∀ (M c : Matrix (Fin D.n) (Fin D.n) A[X]), M ∈ D.V A[X] (Ψ : Set J) →
      mderiv c = M * c → c.map (evalRingHom 0) = 1 →
      ∃ L : List (J × A[X]), (∀ p ∈ L, p.1 ∈ Ψ) ∧
        L.Pairwise (fun p q => p.1 ≠ q.1 ∧ h (P.root p.1) ≤ h (P.root q.1)) ∧
        c = (L.map fun p => divExp (D.e p.1) p.2).prod := by
  classical
  intro Ψ
  induction Ψ using Finset.strongInduction with
  | H Ψ ih =>
  intro hpos hcl M c hM hc h0
  rcases Ψ.eq_empty_or_nonempty with rfl | hne
  · refine ⟨[], by simp, List.Pairwise.nil, ?_⟩
    have hM0 : M = 0 := by
      simpa [V] using hM
    rw [List.map_nil, List.prod_nil]
    exact eq_one_of_mderiv_eq_zero (by rw [hc, hM0, Matrix.zero_mul]) h0
  obtain ⟨ε, hε, hmin⟩ := Ψ.exists_min_image (fun θ => h (P.root θ)) hne
  have hεpos := hpos ε hε
  have hgt : ∀ a ∈ Ψ, ∀ b ∈ Ψ, ∀ m : ℕ, 1 ≤ m → ∀ θ, P.root θ = P.root a + m • P.root b →
      h (P.root a) < h (P.root θ) := by
    intro a _ b hb m hm θ hθ
    have hb' := hpos b hb
    have hθ' : h (P.root θ) = h (P.root a) + m * h (P.root b) := by
      rw [hθ, map_add, map_nsmul, nsmul_eq_mul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hpos' : ∀ θ ∈ Ψ.erase ε, 0 < h (P.root θ) :=
    fun θ hθ => hpos θ (Finset.mem_of_mem_erase hθ)
  have hcl' : ∀ a ∈ Ψ.erase ε, ∀ b ∈ Ψ.erase ε, ∀ m : ℕ, 1 ≤ m → ∀ θ,
      P.root θ = P.root a + m • P.root b → θ ∈ Ψ.erase ε := by
    intro a ha b hb m hm θ hθ
    have ha' := Finset.mem_of_mem_erase ha
    have hb' := Finset.mem_of_mem_erase hb
    refine Finset.mem_erase.mpr ⟨fun hθε => ?_, hcl a ha' b hb' m hm θ hθ⟩
    rw [hθε] at hθ
    have h1 := hgt a ha' b hb' m hm ε hθ
    have h2 : h (P.root ε) ≤ h (P.root a) := hmin a ha'
    omega
  have hclε : ∀ θ ∈ ((Ψ.erase ε : Finset J) : Set J), ∀ m : ℕ, 1 ≤ m → ∀ κ,
      P.root κ = P.root θ + m • P.root ε → κ ∈ ((Ψ.erase ε : Finset J) : Set J) := by
    intro θ hθ m hm κ hκ
    have hθ' := Finset.mem_of_mem_erase (Finset.mem_coe.mp hθ)
    refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun hκε => ?_, hcl θ hθ' ε hε m hm κ hκ⟩)
    rw [hκε] at hκ
    have h1 := hgt θ hθ' ε hε m hm ε hκ
    have h2 : h (P.root ε) ≤ h (P.root θ) := hmin θ hθ'
    omega
  have hins : (Ψ : Set J) = insert ε ((Ψ.erase ε : Finset J) : Set J) := by
    rw [← Finset.coe_insert, Finset.insert_erase hε]
  rw [V, hins, Set.image_insert_eq, Submodule.mem_span_insert] at hM
  obtain ⟨m₀, M₁, hM₁, rfl⟩ := hM
  obtain ⟨F, hF, hF0⟩ := exists_antideriv m₀
  have hM₁' : divExp (D.e ε) (-F) * M₁ * divExp (D.e ε) F ∈
      D.V A[X] ((Ψ.erase ε : Finset J) : Set J) := by
    have := D.conj_mem (R := A[X]) h hεpos (fun θ hθ => hpos' θ hθ) hclε (-F) hM₁
    rwa [neg_neg] at this
  have hcomm : D.E A[X] ε * divExp (D.e ε) (-F) = divExp (D.e ε) (-F) * D.E A[X] ε :=
    (D.commute_E_divExp ε (-F)).eq
  have hc₁ : mderiv (divExp (D.e ε) (-F) * c) =
      (divExp (D.e ε) (-F) * M₁ * divExp (D.e ε) F) * (divExp (D.e ε) (-F) * c) := by
    rw [mderiv_mul, D.mderiv_divExp, hc, derivative_neg, hF]
    calc (-m₀) • (D.E A[X] ε * divExp (D.e ε) (-F)) * c +
          divExp (D.e ε) (-F) * ((m₀ • D.E A[X] ε + M₁) * c)
        = -(m₀ • (D.E A[X] ε * divExp (D.e ε) (-F) * c)) +
            (m₀ • (divExp (D.e ε) (-F) * D.E A[X] ε * c) + divExp (D.e ε) (-F) * M₁ * c) := by
          simp only [neg_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add,
            Matrix.mul_smul, Matrix.mul_assoc]
      _ = divExp (D.e ε) (-F) * M₁ * c := by
          rw [hcomm]
          abel
      _ = (divExp (D.e ε) (-F) * M₁ * divExp (D.e ε) F) * (divExp (D.e ε) (-F) * c) := by
          rw [Matrix.mul_assoc (divExp (D.e ε) (-F) * M₁), ← Matrix.mul_assoc (divExp (D.e ε) F),
            D.divExp_mul_divExp_neg, Matrix.one_mul]
  have h0₁ : (divExp (D.e ε) (-F) * c).map (evalRingHom 0) = 1 := by
    rw [Matrix.map_mul, divExp_map, h0, Matrix.mul_one, coe_evalRingHom, eval_neg,
      ← coeff_zero_eq_eval_zero, hF0, neg_zero, divExp_zero (D.isDividedPowerFamily ε)]
  obtain ⟨L₁, hL₁Ψ, hL₁, hc₁L⟩ :=
    ih (Ψ.erase ε) (Finset.erase_ssubset hε) hpos' hcl' _ _ hM₁' hc₁ h0₁
  refine ⟨(ε, F) :: L₁, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hε
    · exact Finset.mem_of_mem_erase (hL₁Ψ p hp)
  · refine List.pairwise_cons.mpr ⟨fun q hq => ⟨fun he => ?_, ?_⟩, hL₁⟩
    · exact Finset.ne_of_mem_erase (hL₁Ψ q hq) he.symm
    · exact hmin q.1 (Finset.mem_of_mem_erase (hL₁Ψ q hq))
  · rw [List.map_cons, List.prod_cons, ← hc₁L, ← Matrix.mul_assoc, D.divExp_mul_divExp_neg,
      Matrix.one_mul]

end LieRootData

end Langlands.GroupScheme.SplitExistence
