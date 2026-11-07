import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.Interval
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # A finite polynomial quotient retaining a monomial box -/

noncomputable section

universe u v

namespace Langlands.Algebra.PolynomialBoxQuotient

open MvPolynomial

variable {k : Type u} [Field k] {σ : Type v}

/-- The monomial ideal supported outside the lower box. -/
def boxIdeal (N : σ →₀ ℕ) : Ideal (MvPolynomial σ k) :=
  restrictSupportIdeal (R := k) (Set.Iic N)ᶜ (isLowerSet_Iic N).compl

@[simp]
theorem mem_boxIdeal (N : σ →₀ ℕ) (P : MvPolynomial σ k) :
    P ∈ boxIdeal (k := k) N ↔ ∀ a : σ →₀ ℕ, a ≤ N → P.coeff a = 0 := by
  change (↑P.support ⊆ (Set.Iic N)ᶜ) ↔ _
  constructor
  · intro h a ha
    exact notMem_support_iff.mp fun hs => h hs ha
  · intro h a ha han
    exact (mem_support_iff.mp ha) (h a han)

/-- These are exactly the relations setting the indicated variable powers to zero. -/
theorem boxIdeal_eq_span (N : σ →₀ ℕ) :
    boxIdeal (k := k) N =
      Ideal.span (Set.range fun i : σ => (X i : MvPolynomial σ k) ^ (N i + 1)) := by
  classical
  have hgen :
      (Set.range fun i : σ => (X i : MvPolynomial σ k) ^ (N i + 1)) =
        (fun a => monomial a (1 : k)) ''
          Set.range (fun i : σ => Finsupp.single i (N i + 1)) := by
    rw [← Set.range_comp']
    simp only [X_pow_eq_monomial]
  ext P
  rw [mem_boxIdeal, hgen, mem_ideal_span_monomial_image]
  constructor
  · intro h a ha
    have hn : ¬ ∀ i : σ, a i ≤ N i :=
      fun han => (mem_support_iff.mp ha) (h a han)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    exact ⟨Finsupp.single i (N i + 1), ⟨i, rfl⟩,
      Finsupp.single_le_iff.mpr (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hi))⟩
  · intro h a ha
    by_contra hc
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := h a (mem_support_iff.mpr hc)
    have := (Finsupp.single_le_iff.mp hi).trans (ha i)
    omega

/-- The actual quotient ring in which precisely the box coefficients survive. -/
abbrev boxAlgebra (N : σ →₀ ℕ) :=
  MvPolynomial σ k ⧸ boxIdeal (k := k) N

/-- The universal tuple in the quotient. -/
def parameter (N : σ →₀ ℕ) (i : σ) : boxAlgebra (k := k) N :=
  Ideal.Quotient.mkₐ k (boxIdeal N) (X i)

theorem parameter_pow (N : σ →₀ ℕ) (i : σ) :
    parameter (k := k) N i ^ (N i + 1) = 0 := by
  classical
  change (Ideal.Quotient.mkₐ k (boxIdeal N) (X i)) ^ (N i + 1) = 0
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mem_boxIdeal N _).mpr
  intro a ha
  rw [X_pow_eq_monomial, coeff_monomial]
  split_ifs with h
  · have hi := ha i
    rw [← h, Finsupp.single_eq_same] at hi
    omega
  · rfl

/-- Extraction of a retained coefficient from the quotient itself. -/
def coefficient (N : σ →₀ ℕ) (a : σ →₀ ℕ) (ha : a ≤ N) :
    boxAlgebra (k := k) N →ₗ[k] k :=
  ((boxIdeal (k := k) N).restrictScalars k).liftQ (lcoeff k a) fun _P hP =>
    (mem_boxIdeal N _).mp hP a ha

@[simp]
theorem coefficient_mk (N : σ →₀ ℕ) (a : σ →₀ ℕ) (ha : a ≤ N)
    (P : MvPolynomial σ k) :
    coefficient N a ha (Ideal.Quotient.mkₐ k (boxIdeal N) P) = P.coeff a := rfl

theorem aeval_parameter (N : σ →₀ ℕ) :
    MvPolynomial.aeval (parameter (k := k) N) =
      Ideal.Quotient.mkₐ k (boxIdeal N) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [aeval_X, parameter]

/-- Universal nilpotent evaluation recovers each coefficient in the box. -/
theorem coefficient_aeval_parameter (N : σ →₀ ℕ) (a : σ →₀ ℕ) (ha : a ≤ N)
    (P : MvPolynomial σ k) :
    coefficient N a ha (MvPolynomial.aeval (parameter N) P) = P.coeff a := by
  rw [aeval_parameter, coefficient_mk]

/-- All surviving coefficients at once. -/
def coefficients (N : σ →₀ ℕ) :
    boxAlgebra (k := k) N →ₗ[k] (Set.Iic N → k) :=
  LinearMap.pi fun a => coefficient N a.val a.property

@[simp]
theorem coefficients_mk (N : σ →₀ ℕ) (P : MvPolynomial σ k) (a : Set.Iic N) :
    coefficients N (Ideal.Quotient.mkₐ k (boxIdeal N) P) a = P.coeff a.val := rfl

theorem coefficients_injective (N : σ →₀ ℕ) :
    Function.Injective (coefficients (k := k) N) := by
  intro x y h
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (boxIdeal N) x
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (boxIdeal N) y
  apply Ideal.Quotient.eq.mpr
  apply (mem_boxIdeal N _).mpr
  intro a ha
  change lcoeff k a (P - Q) = 0
  rw [map_sub, sub_eq_zero]
  exact congrFun h ⟨a, ha⟩

theorem coefficients_surjective (N : σ →₀ ℕ) :
    Function.Surjective (coefficients (k := k) N) := by
  classical
  intro c
  refine ⟨Ideal.Quotient.mkₐ k (boxIdeal N)
    (∑ a : Set.Iic N, monomial a.val (c a)), ?_⟩
  ext a
  simp only [coefficients_mk, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    exact ite_eq_right (fun h => hba (Subtype.ext h))
  · simp

/-- The quotient has exactly one freely chosen scalar at each box exponent. -/
def coefficientsEquiv (N : σ →₀ ℕ) :
    boxAlgebra (k := k) N ≃ₗ[k] (Set.Iic N → k) :=
  LinearEquiv.ofBijective (coefficients N)
    ⟨coefficients_injective N, coefficients_surjective N⟩

instance finite_boxAlgebra (N : σ →₀ ℕ) : Module.Finite k (boxAlgebra (k := k) N) := by
  classical
  let : Fintype (Set.Iic N) := Fintype.ofFinite _
  exact Module.Finite.equiv (coefficientsEquiv N).symm

theorem finrank_boxAlgebra (N : σ →₀ ℕ) :
    Module.finrank k (boxAlgebra (k := k) N) =
      ∏ i ∈ N.support, (N i + 1) := by
  classical
  let : Fintype (Set.Iic N) := Fintype.ofFinite _
  rw [(coefficientsEquiv (k := k) N).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_of_finset' (p := Set.Iic N) (Finset.Iic N)
      (fun _ => Finset.mem_Iic), Finsupp.card_Iic]
  simp only [Nat.card_Iic]

/-- Multiplication by the complementary monomial recovers any retained
coefficient as the top coefficient. -/
theorem top_coefficient_mul_monomial (N : σ →₀ ℕ) (a : σ →₀ ℕ) (ha : a ≤ N)
    (x : boxAlgebra (k := k) N) :
    coefficient N N le_rfl
      (x * Ideal.Quotient.mkₐ k (boxIdeal N) (monomial (N - a) (1 : k))) =
        coefficient N a ha x := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (boxIdeal N) x
  rw [← map_mul, coefficient_mk, coeff_mul_monomial',
    ite_eq_left (tsub_le_self : N - a ≤ N), mul_one, coefficient_mk]
  have hsub : N - (N - a) = a := by
    ext i
    exact Nat.sub_sub_self (ha i)
  rw [hsub]

/-- The top-coefficient multiplication pairing is nondegenerate. -/
theorem exists_top_coefficient_mul_ne_zero (N : σ →₀ ℕ)
    (x : boxAlgebra (k := k) N) (hx : x ≠ 0) :
    ∃ y : boxAlgebra (k := k) N, coefficient N N le_rfl (x * y) ≠ 0 := by
  classical
  by_contra! h
  apply hx
  apply coefficients_injective N
  ext a
  rw [map_zero]
  exact (top_coefficient_mul_monomial N a.val a.property x).symm.trans (h _)

section UniversalProperty

variable {A : Type*} [CommRing A] [Algebra k A]

/-- Evaluation at any tuple with the prescribed nilpotence bounds kills the ideal. -/
theorem aeval_eq_zero_of_mem_boxIdeal (N : σ →₀ ℕ) (t : σ → A)
    (ht : ∀ i, t i ^ (N i + 1) = 0)
    (P : MvPolynomial σ k) (hP : P ∈ boxIdeal (k := k) N) :
    MvPolynomial.aeval t P = 0 := by
  have hle : boxIdeal (k := k) N ≤ RingHom.ker (MvPolynomial.aeval t).toRingHom := by
    rw [boxIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.aeval t ((X i : MvPolynomial σ k) ^ (N i + 1)) = 0
    simpa only [map_pow, MvPolynomial.aeval_X] using ht i
  exact hle hP

/-- The algebra map classifying a tuple with the prescribed nilpotence bounds. -/
def lift (N : σ →₀ ℕ) (t : σ → A) (ht : ∀ i, t i ^ (N i + 1) = 0) :
    boxAlgebra (k := k) N →ₐ[k] A :=
  Ideal.Quotient.liftₐ (boxIdeal N) (MvPolynomial.aeval t)
    (aeval_eq_zero_of_mem_boxIdeal N t ht)

@[simp]
theorem lift_mk (N : σ →₀ ℕ) (t : σ → A) (ht : ∀ i, t i ^ (N i + 1) = 0)
    (P : MvPolynomial σ k) :
    lift N t ht (Ideal.Quotient.mkₐ k (boxIdeal N) P) = MvPolynomial.aeval t P := rfl

@[simp]
theorem lift_parameter (N : σ →₀ ℕ) (t : σ → A) (ht : ∀ i, t i ^ (N i + 1) = 0)
    (i : σ) :
    lift (k := k) N t ht (parameter (k := k) N i) = t i := by
  simp only [parameter, lift_mk, MvPolynomial.aeval_X]

/-- The parameter values uniquely determine a map from the quotient. -/
theorem lift_unique (N : σ →₀ ℕ) (t : σ → A) (ht : ∀ i, t i ^ (N i + 1) = 0)
    (F : boxAlgebra (k := k) N →ₐ[k] A)
    (hF : ∀ i, F (parameter N i) = t i) :
    F = lift N t ht := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change F (parameter N i) = lift N t ht (parameter N i)
  rw [hF, lift_parameter]

end UniversalProperty

end Langlands.Algebra.PolynomialBoxQuotient
