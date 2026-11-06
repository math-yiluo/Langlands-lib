import Langlands.LocalFactor.UnitaryEuler
import Langlands.LocalFactor.Analytic.ReciprocalEntire
import Langlands.Global.Factors.AppendixPoleCountingStatement
import Mathlib.Analysis.Analytic.Polynomial

/-! # Finite unit-circle Euler products and their actual meromorphic orders -/

noncomputable section

open Filter Polynomial
open scoped Topology

namespace Langlands.LocalFactor

/-- A finite Euler parameter set on the unit circle, with its actual positive
spectral base. No representation-theoretic factor identity is included. -/
structure FiniteUnitaryEuler where
  q : ℝ
  q_gt_one : 1 < q
  parameters : Finset ℂ
  norm_eq_one : ∀ a ∈ parameters, ‖a‖ = 1

namespace FiniteUnitaryEuler

variable (E : FiniteUnitaryEuler)

/-- The normalized finite Euler polynomial. -/
def polynomial : ℂ[X] :=
  ∏ a ∈ E.parameters, (1 - C a * X)

/-- The actual entire denominator at the exponential parameter `q^(-s)`. -/
def denominator (s : ℂ) : ℂ :=
  ∏ a ∈ E.parameters,
    (1 - a * (spectralParameter E.q (lt_trans zero_lt_one E.q_gt_one) s : ℂ))

theorem denominator_eq_eval (s : ℂ) :
    E.denominator s = E.polynomial.eval
      (spectralParameter E.q (lt_trans zero_lt_one E.q_gt_one) s : ℂ) := by
  classical
  simp [denominator, polynomial, eval_prod]

theorem analyticAt_denominator (s : ℂ) :
    AnalyticAt ℂ E.denominator s := by
  classical
  apply E.parameters.analyticAt_fun_prod
  intro a ha
  exact analyticAt_const.sub (analyticAt_const.mul
    ((analyticAt_id.neg.mul analyticAt_const).cexp))

theorem denominator_ne_zero {s : ℂ} (hs : s.re ≠ 0) :
    E.denominator s ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha hz
  have heq : a *
      (spectralParameter E.q (lt_trans zero_lt_one E.q_gt_one) s : ℂ) = 1 :=
    (sub_eq_zero.mp hz).symm
  have hn := congrArg norm heq
  rw [norm_mul, E.norm_eq_one a ha, one_mul, norm_one] at hn
  exact norm_spectralParameter_ne_one E.q_gt_one hs hn

/-- The reciprocal retains its punctured germ at every Euler zero. -/
def reciprocalEntire : ReciprocalEntire where
  denominator := E.denominator
  entire := fun s => (E.analyticAt_denominator s).differentiableAt
  nonzero := ⟨1, E.denominator_ne_zero (by simp)⟩

/-- An ordinary representative of the reciprocal germ. Its value at a pole
does not encode regularity; all pole assertions below use meromorphic order. -/
def reciprocal (s : ℂ) : ℂ := (E.denominator s)⁻¹

theorem meromorphicAt_reciprocal (s : ℂ) :
    MeromorphicAt E.reciprocal s :=
  (E.analyticAt_denominator s).meromorphicAt.inv

theorem reciprocal_order_nonpos (s : ℂ) :
    meromorphicOrderAt E.reciprocal s ≤ 0 := by
  have ha := E.analyticAt_denominator s
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero ha.meromorphicAt).mpr
    (E.reciprocalEntire.denominator_eventually_ne_zero s)
  change meromorphicOrderAt E.denominator⁻¹ s ≤ 0
  rw [meromorphicOrderAt_inv]
  have hp := ha.meromorphicOrderAt_nonneg
  lift meromorphicOrderAt E.denominator s to ℤ using hn with n hn
  exact_mod_cast neg_nonpos.mpr (show (0 : ℤ) ≤ n by exact_mod_cast hp)

theorem holomorphicUnitAt_reciprocal {s : ℂ} (hs : s.re ≠ 0) :
    Global.PoleComparison.HolomorphicUnitAt E.reciprocal s :=
  ⟨(E.analyticAt_denominator s).inv (E.denominator_ne_zero hs),
    inv_ne_zero (E.denominator_ne_zero hs)⟩

theorem denominator_zero (ha : (1 : ℂ) ∈ E.parameters) :
    E.denominator 0 = 0 := by
  classical
  apply Finset.prod_eq_zero ha
  simp [spectralParameter]

theorem reciprocal_order_zero_neg (ha : (1 : ℂ) ∈ E.parameters) :
    meromorphicOrderAt E.reciprocal 0 < 0 := by
  apply lt_of_not_ge
  intro h
  obtain ⟨g, hg, heq⟩ :=
    (E.meromorphicAt_reciprocal 0).meromorphicOrderAt_nonneg_iff.mp h
  apply (E.reciprocalEntire.isPole_iff_no_analytic_germ 0).mp (E.denominator_zero ha)
  exact ⟨g, hg, Germ.coe_eq.mpr heq.symm⟩

/-- The Appendix analytic conditions follow from actual finite unitary Euler
data whenever the matched pair's parameter set contains one. -/
theorem basePairConditions {I : Type*} (partner : I → I)
    (data : I → I → FiniteUnitaryEuler)
    (hpartner : ∀ i, (1 : ℂ) ∈ (data i (partner i)).parameters) :
    Global.PoleComparison.BasePairConditions partner
      (fun i j => (data i j).reciprocal) := by
  refine ⟨fun i j t =>
    ⟨(data i j).meromorphicAt_reciprocal t, (data i j).reciprocal_order_nonpos t⟩,
    fun i j t ht => ?_, fun i => (data i (partner i)).reciprocal_order_zero_neg
      (hpartner i)⟩
  exact (data i j).holomorphicUnitAt_reciprocal (by simpa using ht.ne')

end FiniteUnitaryEuler
end Langlands.LocalFactor
