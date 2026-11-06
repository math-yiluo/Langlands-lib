import Langlands.GroupScheme.Reductive.RankOneSteinbergOperators
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Divided polynomial coefficients and Steinberg monomial boxes -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.SteinbergMonomialBox

open MvPolynomial

variable {k : Type u} [Field k] {σ : Type v}

/-- The multivariate binomial coefficient for a divided polynomial derivative. -/
def dividedBinomial (a b : σ →₀ ℕ) : k :=
  ∏ i ∈ a.support, ((b i).choose (a i) : k)

/-- The divided polynomial derivative with multi-index `a`, specified on the
actual monomial basis. Ordinary derivatives would lose factorials in characteristic p. -/
def dividedPower (a : σ →₀ ℕ) : Module.End k (MvPolynomial σ k) :=
  (basisMonomials σ k).constr k fun b =>
    monomial (b - a) (dividedBinomial (k := k) a b)

@[simp]
theorem dividedPower_monomial_one (a b : σ →₀ ℕ) :
    dividedPower (k := k) a (monomial b 1) =
      monomial (b - a) (dividedBinomial (k := k) a b) :=
  (basisMonomials σ k).constr_basis k _ b

/-- The actual submodule of polynomials whose exponents lie below `N`. -/
def monomialBox (N : σ →₀ ℕ) : Submodule k (MvPolynomial σ k) :=
  restrictSupport k (Set.Iic N)

/-- Its dimension is the number of monomials in the finite coordinatewise box. -/
theorem finrank_monomialBox (N : σ →₀ ℕ) :
    Module.finrank k (monomialBox (k := k) N) =
      ∏ i ∈ N.support, (N i + 1) := by
  classical
  let : Fintype (Set.Iic N) := Fintype.ofFinite _
  rw [monomialBox, Module.finrank_eq_card_basis (basisRestrictSupport k (Set.Iic N))]
  rw [Fintype.card_of_finset' (p := Set.Iic N) (Finset.Iic N)
    (fun _ => Finset.mem_Iic),
    Finsupp.card_Iic]
  simp only [Nat.card_Iic]

/-- Nonzero binomial coefficients recover every monomial in the box from
specified divided derivatives of its top monomial. -/
theorem monomialBox_le_of_dividedPower_top_mem
    (N : σ →₀ ℕ) (W : Submodule k (MvPolynomial σ k))
    (hchoose : ∀ a : σ →₀ ℕ, a ≤ N → dividedBinomial (k := k) a N ≠ 0)
    (hW : ∀ a : σ →₀ ℕ, a ≤ N →
      dividedPower (k := k) a (monomial N 1) ∈ W) :
    monomialBox (k := k) N ≤ W := by
  rw [monomialBox, restrictSupport_eq_span, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  change monomial m (1 : k) ∈ W
  have ha : N - m ≤ N := tsub_le_self
  have hcoeff := hchoose (N - m) ha
  have h := W.smul_mem (dividedBinomial (k := k) (N - m) N)⁻¹ (hW (N - m) ha)
  have hsub : N - (N - m) = m := by
    ext i
    exact Nat.sub_sub_self (hm i)
  simpa only [dividedPower_monomial_one, hsub, smul_monomial, smul_eq_mul,
    inv_mul_cancel₀ hcoeff] using h

/-- At a Steinberg exponent in every used coordinate, all required
multivariate binomial coefficients are nonzero. -/
theorem dividedBinomial_ne_zero_of_steinberg
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ) (N : σ →₀ ℕ)
    (hN : ∀ i ∈ N.support, N i = p ^ r - 1)
    (a : σ →₀ ℕ) (ha : a ≤ N) :
    dividedBinomial (k := k) a N ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hai : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hNi : i ∈ N.support := Finsupp.mem_support_iff.mpr (by
    intro hzero
    have hle := ha i
    rw [hzero] at hle
    exact hai (Nat.eq_zero_of_le_zero hle))
  rw [hN i hNi]
  exact RankOneSteinberg.choose_steinberg_cast_ne_zero p r (a i) (by
    simpa only [hN i hNi] using ha i)

/-- The Steinberg binomial calculation supplies the entire lower box. -/
theorem monomialBox_le_of_steinberg_dividedPower_top_mem
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ) (N : σ →₀ ℕ)
    (hN : ∀ i ∈ N.support, N i = p ^ r - 1)
    (W : Submodule k (MvPolynomial σ k))
    (hW : ∀ a : σ →₀ ℕ, a ≤ N →
      dividedPower (k := k) a (monomial N 1) ∈ W) :
    monomialBox (k := k) N ≤ W :=
  monomialBox_le_of_dividedPower_top_mem N W
    (dividedBinomial_ne_zero_of_steinberg p r N hN) hW

/-- If a finite space has all those derivatives in its polynomial image,
its dimension is at least the number of monomials in the box. -/
theorem product_le_finrank_of_dividedPower_top_mem_range
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (L : V →ₗ[k] MvPolynomial σ k) (N : σ →₀ ℕ)
    (hchoose : ∀ a : σ →₀ ℕ, a ≤ N → dividedBinomial (k := k) a N ≠ 0)
    (hL : ∀ a : σ →₀ ℕ, a ≤ N →
      dividedPower (k := k) a (monomial N 1) ∈ LinearMap.range L) :
    (∏ i ∈ N.support, (N i + 1)) ≤ Module.finrank k V := by
  have hle := monomialBox_le_of_dividedPower_top_mem N (LinearMap.range L) hchoose hL
  rw [← finrank_monomialBox (k := k) N]
  exact (LinearMap.finrank_le_finrank_of_injective
    (Submodule.inclusion_injective hle)).trans (LinearMap.finrank_range_le L)

end Langlands.GroupScheme.SteinbergMonomialBox
