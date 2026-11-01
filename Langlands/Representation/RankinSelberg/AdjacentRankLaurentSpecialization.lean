import Langlands.Representation.RankinSelberg.AdjacentRankParameterSpecialization
import Langlands.HarmonicAnalysis.BilateralLaurentSeries

/-! Uniform finite support and actual bilateral Laurent clearing under entire deformation. -/

noncomputable section

namespace Langlands.RankinSelberg.ParameterSpecialization

open HarmonicAnalysis
open scoped BigOperators

/-- One finite exponent set supports the coefficient family at every parameter. -/
def UniformlyFiniteCoefficientSupport (c : ℂ → ℤ → ℂ) : Prop :=
  ∃ S : Finset ℤ, ∀ u m, m ∉ S → c u m = 0

/-- Pointwise finite support on an uncountable parameter set gives one common
finite support for an entire coefficient family at all complex parameters. -/
theorem uniformlyFiniteSupport_of_uncountable
    {c : ℂ → ℤ → ℂ} (hc : EntireCoefficientFamily c)
    (hfinite : ¬ {u : ℂ | {m : ℤ | c u m ≠ 0}.Finite}.Countable) :
    UniformlyFiniteCoefficientSupport c := by
  classical
  let A : Finset ℤ → Set ℂ := fun S => {u | ∀ m, m ∉ S → c u m = 0}
  have hcover : {u : ℂ | {m : ℤ | c u m ≠ 0}.Finite} = ⋃ S, A S := by
    ext u
    constructor
    · intro hu
      refine Set.mem_iUnion.mpr ⟨hu.toFinset, ?_⟩
      intro m hm
      by_contra hne
      exact hm (hu.mem_toFinset.mpr hne)
    · intro hu
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hu
      exact S.finite_toSet.subset (fun m hm => by
        by_contra hnot
        exact hm (hS m hnot))
  have hunc : ∃ S : Finset ℤ, ¬ (A S).Countable := by
    by_contra hn
    push Not at hn
    apply hfinite
    rw [hcover]
    exact Set.countable_iUnion hn
  obtain ⟨S, hS⟩ := hunc
  refine ⟨S, fun u m hm => ?_⟩
  exact TwoBlockDeformation.eq_zero_of_not_countable
    (fun z => (hc m z).differentiableAt)
    (fun hz => hS (hz.mono (fun z hz => hz m hm))) u

/-- The common finite support follows from pointwise finite support for all
sufficiently large positive real parameters, without a uniform degree premise. -/
theorem uniformlyFiniteSupport_of_real_gt
    {c : ℂ → ℤ → ℂ} (hc : EntireCoefficientFamily c) (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → {m : ℤ | c (u : ℂ) m ≠ 0}.Finite) :
    UniformlyFiniteCoefficientSupport c := by
  have hinj : Function.Injective (fun x : ℝ => ((C + Real.exp x : ℝ) : ℂ)) := by
    intro x y h
    exact Real.exp_injective (add_left_cancel (Complex.ofReal_injective h))
  apply uniformlyFiniteSupport_of_uncountable hc
  intro hcount
  apply Cardinal.not_countable_real
  refine (hcount.preimage hinj).mono ?_
  intro x _
  exact hreal (C + Real.exp x) (by linarith [Real.exp_pos x])

/-- With a common finite kernel support, the auxiliary finite convolution is
exactly the published Laurent-polynomial action on actual bilateral series. -/
theorem laurent_smul_eq_finiteCombination
    (S : Finset ℤ) (P : ℂ → LaurentPolynomial ℂ) (c : ℂ → BilateralLaurentSeries)
    (hP : ∀ u, (P u).coeff.support ⊆ S) :
    (fun u => P u • c u) =
      finiteLaurentCombination S (fun u j => (P u).coeff j) c := by
  classical
  funext u m
  rw [BilateralLaurentSeries.laurent_smul_apply]
  change (∑ j ∈ (P u).coeff.support, (P u).coeff j * c u (m - j)) =
    ∑ j ∈ S, (P u).coeff j * c u (m - j)
  exact Finset.sum_subset (hP u) (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, zero_mul])

/-- Actual Laurent-polynomial clearing with a common finite kernel support
preserves coefficientwise entire dependence. -/
theorem laurent_smul_entire
    (S : Finset ℤ) (P : ℂ → LaurentPolynomial ℂ) (c : ℂ → BilateralLaurentSeries)
    (hP : ∀ u, (P u).coeff.support ⊆ S)
    (hPa : ∀ j ∈ S, ∀ u, AnalyticAt ℂ (fun z => (P z).coeff j) u)
    (hc : EntireCoefficientFamily c) :
    EntireCoefficientFamily (fun u => P u • c u) := by
  rw [laurent_smul_eq_finiteCombination S P c hP]
  exact finiteLaurentCombination_entire S hPa hc

/-- Pointwise Laurent-polynomial clearing above a real bound extends to an
actual Laurent-polynomial family at every parameter, with common finite support.
No uniform degree bound on the cleared output is assumed. -/
theorem laurent_clearing_of_real_gt
    (S : Finset ℤ) (P : ℂ → LaurentPolynomial ℂ) (c : ℂ → BilateralLaurentSeries)
    (hP : ∀ u, (P u).coeff.support ⊆ S)
    (hPa : ∀ j ∈ S, ∀ u, AnalyticAt ℂ (fun z => (P z).coeff j) u)
    (hc : EntireCoefficientFamily c) (C : ℝ)
    (hreal : ∀ u : ℝ, C < u → ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R = P (u : ℂ) • c (u : ℂ)) :
    ∃ Q : ℂ → LaurentPolynomial ℂ,
      (∀ u, BilateralLaurentSeries.ofLaurentPolynomial (Q u) = P u • c u) ∧
      (∃ T : Finset ℤ, ∀ u, (Q u).coeff.support ⊆ T) ∧
      EntireCoefficientFamily (fun u j => (Q u).coeff j) := by
  classical
  have hcleared := laurent_smul_entire S P c hP hPa hc
  have hfinite : ∀ u : ℝ, C < u →
      {m : ℤ | (P (u : ℂ) • c (u : ℂ)) m ≠ 0}.Finite := by
    intro u hu
    obtain ⟨R, hR⟩ := hreal u hu
    rw [← hR]
    convert R.coeff.support.finite_toSet using 1
    ext m
    simp
  obtain ⟨T, hT⟩ := uniformlyFiniteSupport_of_real_gt hcleared C hfinite
  have hfin (u : ℂ) : {m : ℤ | (P u • c u) m ≠ 0}.Finite :=
    T.finite_toSet.subset fun m hm => by
      by_contra hnot
      exact hm (hT u m hnot)
  let Q : ℂ → LaurentPolynomial ℂ := fun u =>
    AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun m => (P u • c u) m) (hfin u))
  have hQ : ∀ u m, (Q u).coeff m = (P u • c u) m := by
    intro u m
    rfl
  refine ⟨Q, ?_, ⟨T, ?_⟩, ?_⟩
  · intro u
    ext m
    exact hQ u m
  · intro u m hm
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hm) ((hQ u m).trans (hT u m hnot))
  · intro m u
    simpa only [hQ] using hcleared m u

end Langlands.RankinSelberg.ParameterSpecialization
