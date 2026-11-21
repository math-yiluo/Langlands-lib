import Langlands.Global.Factors.FiniteEpsilonBaseComparison
import Mathlib.Algebra.Polynomial.Expand

/-! # Finite Euler values and positive epsilon bases at auxiliary places -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace Langlands.BaseChange

open Global.FunctionalEquationComparison
open _root_.Polynomial

universe u v w

private theorem prod_restriction_of_card {X A M : Type*} [Fintype X] [Fintype A]
    [DecidableEq A] [CommMonoid M] (res : X → A) (m : ℕ)
    (hres : ∀ a : A, Fintype.card {x : X // res x = a} = m) (g : A → M) :
    (∏ x, g (res x)) = (∏ a, g a) ^ m := by
  rw [← Fintype.prod_fiberwise' res g, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun a _ => by simp [hres a]

private theorem spectralPoint_pow_cardinality (q f : ℕ) (z : ℂ) :
    RankinSelberg.spectralPoint (q ^ f) z = RankinSelberg.spectralPoint q z ^ f := by
  rw [RankinSelberg.spectralPoint, RankinSelberg.spectralPoint, Nat.cast_pow,
    ← Complex.cpow_nat_mul, Complex.cpow_nat_mul' (by simp [Complex.natCast_arg, Real.pi_pos])
      (by simp [Complex.natCast_arg, Real.pi_pos.le])]

private theorem prod_natCast_zpow {A : Type*} (S : Finset A) {q : ℕ} (hq : 0 < q)
    (m : A → ℤ) : (∏ a ∈ S, (q : ℝ) ^ m a) = (q : ℝ) ^ (∑ a ∈ S, m a) := by
  classical
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq']

/-- Suppose every local twist has as many global extensions as there are
places above the base place, and the upper data are the same at those places.
The residue-degree substitution and the exponent sum then give the Euler
value comparison and the positive epsilon base comparison for that fiber. -/
def AuxiliaryFactorProductComparisonStatement : Prop :=
  ∀ (X : Type u) [Fintype X] (A : Type v) [Fintype A] [DecidableEq A] (W : Type w) [Fintype W]
    (res : X → A), (∀ a : A, Fintype.card {x : X // res x = a} = Fintype.card W) →
    ∀ (qF qE f : ℕ), 0 < qF → qE = qF ^ f →
    ∀ (P : A → ℂ[X]) (Q : ℂ[X]) (PF : X → ℂ[X]) (PE : W → ℂ[X])
      (m : A → ℤ) (n : ℤ) (bF : X → ℂˣ × ℤ) (bE : W → ℂˣ × ℤ),
      (∏ a, P a) = expand ℂ f Q → (∑ a, m a) = (f : ℤ) * n →
      (∀ x, PF x = P (res x)) → (∀ w, PE w = Q) →
      (∀ x, (bF x).2 = m (res x)) → (∀ w, (bE w).2 = n) →
      (∀ z : ℂ, (∏ x, ((PF x).eval (RankinSelberg.spectralPoint qF z))⁻¹) =
        ∏ w, ((PE w).eval (RankinSelberg.spectralPoint qE z))⁻¹) ∧
      finiteEpsilonBase Finset.univ (fun _ : X => qF) bF =
        finiteEpsilonBase Finset.univ (fun _ : W => qE) bE

theorem auxiliaryFactorProductComparison : AuxiliaryFactorProductComparisonStatement.{u, v, w} := by
  intro X _ A _ _ W _ res hres qF qE f hqF hqE P Q PF PE m n bF bE hP hm hPF hPE hmF hmE
  constructor
  · intro z
    have hQ := congrArg (Polynomial.eval (RankinSelberg.spectralPoint qF z)) hP
    rw [eval_prod, expand_eval, ← spectralPoint_pow_cardinality, ← hqE] at hQ
    simp_rw [hPF, hPE]
    rw [prod_restriction_of_card res (Fintype.card W) hres
      (fun a => ((P a).eval (RankinSelberg.spectralPoint qF z))⁻¹),
      Finset.prod_inv_distrib, hQ]
    simp
  · have he : (∏ a, (qF : ℝ) ^ m a) = (qE : ℝ) ^ n := by
      rw [prod_natCast_zpow Finset.univ hqF, hm, hqE, Nat.cast_pow, zpow_mul, zpow_natCast]
    simp only [finiteEpsilonBase, hmF, hmE]
    rw [prod_restriction_of_card res (Fintype.card W) hres (fun a => (qF : ℝ) ^ m a), he]
    simp

end Langlands.BaseChange
