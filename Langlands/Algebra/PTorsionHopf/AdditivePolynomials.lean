import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Perfect

/-! # One-variable additive polynomials in prime characteristic -/

noncomputable section

universe u

open Polynomial

namespace Langlands.Algebra.PTorsionHopf

variable {k : Type u} [Field k]

/-- A one-variable polynomial is additive if `f(a + b) = f(a) + f(b)` in every commutative
`k`-algebra of the same universe. -/
def IsAdditivePoly (f : k[X]) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (a b : R), aeval (a + b) f = aeval a f + aeval b f

theorem IsAdditivePoly.sub {f g : k[X]} (hf : IsAdditivePoly f) (hg : IsAdditivePoly g) :
    IsAdditivePoly (f - g) := fun R _ _ a b => by
  rw [map_sub, map_sub, map_sub, hf R a b, hg R a b]
  ring

theorem IsAdditivePoly.comp {f g : k[X]} (hf : IsAdditivePoly f) (hg : IsAdditivePoly g) :
    IsAdditivePoly (f.comp g) := fun R _ _ a b => by
  rw [aeval_comp, aeval_comp, aeval_comp, hg R a b, hf R]

/-- Frobenius powers are additive in every algebra over a field of characteristic `p`. -/
theorem add_pow_char_pow_of_algebra (p : ℕ) [Fact p.Prime] [CharP k p] {R : Type*}
    [CommRing R] [Algebra k R] (n : ℕ) (a b : R) :
    (a + b) ^ p ^ n = a ^ p ^ n + b ^ p ^ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact Subsingleton.elim _ _
  · have := charP_of_injective_algebraMap (algebraMap k R).injective p
    exact add_pow_char_pow a b p n

theorem isAdditivePoly_C_mul_X_pow (p : ℕ) [Fact p.Prime] [CharP k p] (c : k) (n : ℕ) :
    IsAdditivePoly (C c * X ^ p ^ n : k[X]) := fun R _ _ a b => by
  simp only [map_mul, aeval_C, map_pow, aeval_X]
  rw [add_pow_char_pow_of_algebra (k := k) p n a b, mul_add]

/-- The additivity identity in two variables: `f(Y + X) = f(X) + f(Y)` in `k[X][Y]`. -/
theorem IsAdditivePoly.taylor_eq {f : k[X]} (hf : IsAdditivePoly f) :
    taylor (X : k[X]) (f.map C) = f.map C + C f := by
  have h := hf (k[X][X]) (X : k[X][X]) (C X)
  have hA : algebraMap k k[X][X] = (C : k[X] →+* k[X][X]).comp C := rfl
  have e1 : aeval (X + C X : k[X][X]) f = taylor (X : k[X]) (f.map C) := by
    rw [taylor_apply, Polynomial.comp, eval₂_map, aeval_def, hA]
  have e2 : aeval (X : k[X][X]) f = f.map C := by
    rw [aeval_def, hA]
    conv_rhs => rw [← eval₂_C_X (p := f.map C), eval₂_map]
  have e3 : aeval (C X : k[X][X]) f = C f := by
    rw [aeval_def, hA, ← Polynomial.hom_eval₂, eval₂_C_X]
  rw [← e1, h, e2, e3]

/-- **Degrees of additive polynomials.** A nonzero additive polynomial over a field of
characteristic `p` has positive degree, a power of `p`. -/
theorem IsAdditivePoly.natDegree_eq_pow (p : ℕ) [Fact p.Prime] [CharP k p] {f : k[X]}
    (hf : IsAdditivePoly f) (hf0 : f ≠ 0) :
    0 < f.natDegree ∧ ∃ e : ℕ, f.natDegree = p ^ e := by
  have hpos : 0 < f.natDegree := by
    by_contra h
    push Not at h
    have hd : f.natDegree = 0 := by omega
    obtain ⟨c, rfl⟩ : ∃ c, f = C c := ⟨f.coeff 0, eq_C_of_natDegree_eq_zero hd⟩
    have := hf k (0 : k) 0
    simp only [add_zero, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] at this
    have hc : c = 0 := by linear_combination -this
    exact hf0 (by rw [hc, map_zero])
  refine ⟨hpos, multiplicity p f.natDegree,
    Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hpos fun i hi => ?_⟩
  rw [Finset.mem_Icc] at hi
  have ht := congrArg (fun g => (g.coeff i).coeff (f.natDegree - i)) hf.taylor_eq
  rw [taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X, hasseDeriv_coeff, coeff_add,
    coeff_map, coeff_C, ite_eq_right (by omega : i ≠ 0), add_zero, coeff_C,
    ite_eq_right (by omega : f.natDegree - i ≠ 0), Nat.sub_add_cancel (by omega : i ≤ f.natDegree)] at ht
  have hlc : f.coeff f.natDegree ≠ 0 := by
    rw [← leadingCoeff]
    exact leadingCoeff_ne_zero.2 hf0
  have hcast : ((f.natDegree.choose i : ℕ) : k) = 0 := by
    rcases mul_eq_zero.1 ht with h | h
    · exact h
    · exact absurd h hlc
  rw [CharP.cast_eq_zero_iff k p] at hcast
  exact Nat.modEq_zero_iff_dvd.2 hcast

end Langlands.Algebra.PTorsionHopf
