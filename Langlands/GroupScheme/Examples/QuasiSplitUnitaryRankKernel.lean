import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.MultiplicativeLaurent

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- A single integral weight on at least two coordinates has a nonzero integral kernel vector. -/
theorem exists_ne_zero_sum_mul_eq_zero {I : Type u} [Fintype I]
    (hI : 2 ≤ Nat.card I) (a : I → ℤ) :
    ∃ m : I → ℤ, m ≠ 0 ∧ ∑ i, a i * m i = 0 := by
  classical
  obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp (by
    rw [← Nat.card_eq_fintype_card]
    omega : 1 < Fintype.card I)
  have hsum (i : I) (r : ℤ) : ∑ k, a k * (Pi.single i r : I → ℤ) k = a i * r := by
    simp [Pi.single_apply]
  by_cases hi : a i = 0
  · refine ⟨Pi.single i 1, ?_, ?_⟩
    · intro hm
      have h := congrFun hm i
      simp at h
    · rw [hsum, hi, zero_mul]
  · refine ⟨Pi.single i (a j) - Pi.single j (a i), ?_, ?_⟩
    · intro hm
      have h := congrFun hm j
      simp only [Pi.sub_apply, Pi.single_eq_of_ne hij.symm, Pi.single_eq_same,
        zero_sub, Pi.zero_apply, neg_eq_zero] at h
      exact hi h
    · simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hsum]
      exact sub_eq_zero.mpr (mul_comm _ _)

/-- Evaluating a weight on powers of one unit is its integral dot-product power. -/
theorem exponentValue_powers {I : Type u} [Fintype I] [DecidableEq I]
    {A : Type u} [CommRing A] (t : Aˣ) (m a : I → ℤ) :
    splitTorus.exponentValue I (fun i => t ^ m i) (Multiplicative.ofAdd a) =
      t ^ (∑ i, a i * m i) := by
  change (∏ i, (t ^ m i) ^ a i) = _
  simp_rw [← zpow_mul, mul_comm (m _) (a _)]
  have hs (s : Finset I) : (∏ i ∈ s, t ^ (a i * m i)) = t ^ (∑ i ∈ s, a i * m i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]
  exact hs Finset.univ

/-- Specializing independent monomials to powers of a Laurent parameter computes a dot product. -/
theorem evaluateUnits_laurent_powers_single (R : CommRingCat.{u}) {I : Type u}
    [Fintype I] [DecidableEq I] (m a : I → ℤ) (r : R) :
    splitTorus.evaluateUnits (R := R) I (fun i => Gm.relativeCoordUnit R ^ m i)
      (AddMonoidAlgebra.single a r) =
        LaurentPolynomial.C r * LaurentPolynomial.T (∑ i, a i * m i) := by
  rw [splitTorus.evaluateUnits_single, exponentValue_powers, Gm.relativeCoordUnit_zpow_val]
  rfl

/-- Different powers of the Laurent parameter are different units over every nonzero ring. -/
theorem relativeCoordUnit_zpow_injective (R : Type u) [CommRing R] [Nontrivial R] :
    Function.Injective (fun m : ℤ => Gm.relativeCoordUnit R ^ m) := by
  intro a b h
  apply Finsupp.single_left_injective (one_ne_zero : (1 : R) ≠ 0)
  have hc := congrArg (fun x : R[T;T⁻¹]ˣ => x.val.coeff) h
  simpa only [Gm.relativeCoordUnit_zpow_val, LaurentPolynomial.T,
    AddMonoidAlgebra.coeff_single] using hc

/-- A Laurent-valued split-torus point with a prescribed exponent vector. -/
def laurentPowerPoint (R : CommRingCat.{u}) (I : Type u) [Finite I] (m : I → ℤ) :
    Lie.AffinePoints (splitTorus (Spec R) I) R[T;T⁻¹] :=
  (splitTorus.algebraPointsEquiv I R[T;T⁻¹]).symm (fun i => Gm.relativeCoordUnit R ^ m i)

/-- A nonzero exponent vector gives a nonidentity point on the actual split torus. -/
theorem laurentPowerPoint_ne_one (R : CommRingCat.{u}) [Nontrivial R]
    (I : Type u) [Finite I] (m : I → ℤ) (hm : m ≠ 0) :
    laurentPowerPoint R I m ≠ 1 := by
  intro h
  apply hm
  funext i
  have hi := congrArg (fun x => splitTorus.algebraPointsEquiv I R[T;T⁻¹] x i) h
  simp only [laurentPowerPoint, MulEquiv.apply_symm_apply, map_one, Pi.one_apply] at hi
  exact relativeCoordUnit_zpow_injective R (hi.trans (zpow_zero _).symm)

end Langlands.GroupScheme.QuasiSplitUnitary
