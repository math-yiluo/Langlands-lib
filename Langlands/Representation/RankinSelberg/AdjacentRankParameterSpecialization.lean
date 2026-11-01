import Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalysis
import Mathlib.Analysis.Real.Cardinality

/-! Coefficientwise specialization of entire parameter families after finite Laurent clearing. -/

noncomputable section

namespace Langlands.RankinSelberg.ParameterSpecialization

open scoped BigOperators

/-- Each determinant-order coefficient is entire in the deformation parameter. -/
def EntireCoefficientFamily (c : ℂ → ℤ → ℂ) : Prop :=
  ∀ m u, AnalyticAt ℂ (fun z => c z m) u

/-- The coefficient of a finite Laurent kernel times an arbitrary two-sided
coefficient family. The finite exponent set is independent of the parameter. -/
def finiteLaurentCombination (S : Finset ℤ) (a c : ℂ → ℤ → ℂ) : ℂ → ℤ → ℂ :=
  fun u m => ∑ j ∈ S, a u j * c u (m - j)

/-- An entire function vanishing on a positive real parameter ray is zero.
This uses the published uncountable-zero-set identity theorem. -/
theorem eq_zero_of_real_gt {f : ℂ → ℂ}
    (hf : ∀ u, AnalyticAt ℂ f u) (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → f (u : ℂ) = 0) (z : ℂ) : f z = 0 := by
  have hinj : Function.Injective (fun x : ℝ => ((C + Real.exp x : ℝ) : ℂ)) := by
    intro x y h
    exact Real.exp_injective (add_left_cancel (Complex.ofReal_injective h))
  have huncountable : ¬ {u : ℂ | f u = 0}.Countable := by
    intro hc
    apply Cardinal.not_countable_real
    refine (hc.preimage hinj).mono ?_
    intro x _
    exact hreal (C + Real.exp x) (by linarith [Real.exp_pos x])
  exact TwoBlockDeformation.eq_zero_of_not_countable
    (fun u => (hf u).differentiableAt) huncountable z

/-- Equality of entire functions on a positive real parameter ray extends
to every complex parameter. -/
theorem eq_of_real_gt {f g : ℂ → ℂ}
    (hf : ∀ u, AnalyticAt ℂ f u) (hg : ∀ u, AnalyticAt ℂ g u) (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → f (u : ℂ) = g (u : ℂ)) : f = g := by
  funext z
  exact sub_eq_zero.mp (eq_zero_of_real_gt (fun u => (hf u).sub (hg u)) C
    (fun u hu => sub_eq_zero.mpr (hreal u hu)) z)

/-- There is no finiteness assumption on the determinant-order index set:
the identity theorem is applied separately to every coefficient. -/
theorem coefficientFamily_eq_of_real_gt {c d : ℂ → ℤ → ℂ}
    (hc : EntireCoefficientFamily c) (hd : EntireCoefficientFamily d)
    (C : ℝ) (hreal : ∀ u : ℝ, C < u → ∀ m, c (u : ℂ) m = d (u : ℂ) m) :
    c = d := by
  funext z m
  exact congrFun (eq_of_real_gt (hc m) (hd m) C (fun u hu => hreal u hu m)) z

/-- Finite Laurent clearing preserves coefficientwise entire dependence.
Both the kernel coefficients and the original coefficients are actual data. -/
theorem finiteLaurentCombination_entire (S : Finset ℤ) {a c : ℂ → ℤ → ℂ}
    (ha : ∀ j ∈ S, ∀ u, AnalyticAt ℂ (fun z => a z j) u)
    (hc : EntireCoefficientFamily c) :
    EntireCoefficientFamily (finiteLaurentCombination S a c) := by
  intro m u
  have hdiff : Differentiable ℂ (fun z => ∑ j ∈ S, a z j * c z (m - j)) :=
    fun z => DifferentiableAt.fun_sum fun j hj =>
      ((ha j hj z).differentiableAt).mul ((hc (m - j) z).differentiableAt)
  exact hdiff.analyticAt u

/-- A polynomial-cleared coefficient identity with fixed finite Laurent
kernels, proved on a positive real parameter ray, specializes to all parameters. -/
theorem finiteLaurentCombination_eq_of_real_gt (S T : Finset ℤ)
    {a b c d : ℂ → ℤ → ℂ}
    (ha : ∀ j ∈ S, ∀ u, AnalyticAt ℂ (fun z => a z j) u)
    (hb : ∀ j ∈ T, ∀ u, AnalyticAt ℂ (fun z => b z j) u)
    (hc : EntireCoefficientFamily c) (hd : EntireCoefficientFamily d)
    (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → ∀ m,
      finiteLaurentCombination S a c (u : ℂ) m =
        finiteLaurentCombination T b d (u : ℂ) m) :
    finiteLaurentCombination S a c = finiteLaurentCombination T b d :=
  coefficientFamily_eq_of_real_gt
    (finiteLaurentCombination_entire S ha hc)
    (finiteLaurentCombination_entire T hb hd) C hreal

end Langlands.RankinSelberg.ParameterSpecialization
