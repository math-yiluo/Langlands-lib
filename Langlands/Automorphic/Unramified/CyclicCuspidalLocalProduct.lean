import Langlands.Global.RankinSelberg.EqualEulerLocalSum
import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Representation.Unramified.EigenvalueScaling
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! # The local cyclic norm-character product for cuspidal pairs -/

noncomputable section

set_option autoImplicit false

open Polynomial

namespace Langlands.Automorphic.Unramified

open Langlands.Unramified
open Langlands.Global.CuspidalPairFunctionalEquation (pairEulerPolynomial)

private theorem prod_sub_mul_pow {ζ : ℂ} {d f : ℕ} (hf : 0 < f)
    (hζ : IsPrimitiveRoot ζ f) (hfd : f ∣ d) (x : ℂ) :
    (∏ i : Fin d, (1 - ζ ^ (i : ℕ) * x)) = (1 - x ^ f) ^ (d / f) := by
  let _ : NeZero f := ⟨hf.ne'⟩
  have hroots : (Finset.range f).image (fun i => ζ ^ i) = nthRootsFinset f (1 : ℂ) := by
    ext ξ
    simp only [Finset.mem_image, Finset.mem_range, mem_nthRootsFinset hf]
    constructor
    · rintro ⟨i, _, rfl⟩
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · exact hζ.eq_pow_of_pow_eq_one
  have hbase : (∏ i ∈ Finset.range f, (1 - ζ ^ i * x)) = 1 - x ^ f := by
    calc
      (∏ i ∈ Finset.range f, (1 - ζ ^ i * x)) =
          ∏ y ∈ (Finset.range f).image (fun i => ζ ^ i), (1 - y * x) := by
        symm
        apply Finset.prod_image
        intro i hi j hj hij
        exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
      _ = 1 - x ^ f := by
        rw [hroots, ← hζ.pow_sub_pow_eq_prod_sub_mul 1 x hf, one_pow]
  have hblocks (k : ℕ) :
      (∏ i ∈ Finset.range (f * k), (1 - ζ ^ i * x)) = (1 - x ^ f) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hperiod : ζ ^ (f * k) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
      rw [Nat.mul_succ, Finset.prod_range_add, ih, pow_succ]
      simp only [pow_add, hperiod, one_mul, hbase]
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 - ζ ^ i * x)]
  calc
    (∏ i ∈ Finset.range d, (1 - ζ ^ i * x)) =
        ∏ i ∈ Finset.range (f * (d / f)), (1 - ζ ^ i * x) := by
      rw [Nat.mul_div_cancel' hfd]
    _ = _ := hblocks (d / f)

/-- At a place of residue degree `f`, the product over `d` character powers of
 the twisted pair denominators is the powered pair denominator repeated `d / f` times. -/
def CyclicCuspidalLocalProductStatement : Prop :=
  ∀ {n m d f : ℕ} (a : Eigenvalues n) (b : Eigenvalues m) (ζ : ℂˣ) (x : ℂ),
    0 < f → IsPrimitiveRoot ζ f → f ∣ d →
    (∏ i : Fin d, (pairEulerPolynomial (a.scale (ζ ^ (i : ℕ))) b).eval x) =
      ((pairEulerPolynomial (a.power f) (b.power f)).eval (x ^ f)) ^ (d / f)

/-- The local identity in the cyclic norm-character product of Arthur–Clozel III.3.1. -/
theorem cyclicCuspidalLocalProduct : CyclicCuspidalLocalProductStatement := by
  intro n m d f a b ζ x hf hζ hfd
  obtain ⟨a, rfl⟩ := Eigenvalues.ofTuple_surjective n a
  obtain ⟨b, rfl⟩ := Eigenvalues.ofTuple_surjective m b
  simp only [Eigenvalues.scale_ofTuple, Eigenvalues.power_ofTuple,
    Langlands.Global.RankinSelbergGlobal.EqualEulerLocal.eval_pairEulerPolynomial_ofTuple, Units.val_mul, Units.val_pow_eq_pow_val]
  let term (k : Fin d) (i : Fin n) (j : Fin m) :=
    1 - ((ζ : ℂ) ^ (k : ℕ) * a i) * b j * x
  calc
    (∏ k, ∏ i, ∏ j, term k i j) = ∏ i, ∏ k, ∏ j, term k i j := Finset.prod_comm
    _ = ∏ i, ∏ j, ∏ k, term k i j := by
      exact Finset.prod_congr rfl fun _ _ => Finset.prod_comm
    _ = ∏ i, ∏ j, (1 - ((a i : ℂ) * b j * x) ^ f) ^ (d / f) := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      simpa only [term, mul_assoc] using
        prod_sub_mul_pow hf (IsPrimitiveRoot.coe_units_iff.mpr hζ) hfd ((a i : ℂ) * b j * x)
    _ = _ := by simp only [mul_pow, Finset.prod_pow]

end Langlands.Automorphic.Unramified
