import Langlands.Global.Factors.TwoTwistGammaOrder

/-! # Two-twist isolation with matching auxiliary gamma orders -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.FunctionalEquationComparison

private theorem finiteGamma_order_eq_order_sum {P : Type u} {D : FiniteEulerData P}
    {S A : Finset P} (hD : Admissible D S) (hA : A ⊆ S) (z : ℂ) :
    meromorphicOrderAt (D.finiteGamma A) z =
      ∑ v ∈ A, meromorphicOrderAt (D.localFactors v).gamma z :=
  meromorphicOrderAt_fun_prod fun v hv => (admissible_gamma_nonzero hD v (hA hv)).1 z

private theorem finiteGamma_order_sum_ne_top {P : Type u} {D : FiniteEulerData P}
    {S A : Finset P} (hD : Admissible D S) (hA : A ⊆ S) (z : ℂ) :
    ∑ v ∈ A, meromorphicOrderAt (D.localFactors v).gamma z ≠ ⊤ :=
  WithTop.sum_ne_top.mpr fun v hv => (admissible_gamma_nonzero hD v (hA hv)).2 z

private theorem retained_order_match {P : Type u} [DecidableEq P]
    {D E : FiniteEulerData P} {S A : Finset P} (hAS : A ⊆ S)
    (h : ComparisonInputs D E S) (z : ℂ)
    (haux : ∀ v ∈ S, v ∉ A → meromorphicOrderAt (D.localFactors v).gamma z =
      meromorphicOrderAt (E.localFactors v).gamma z) :
    meromorphicOrderAt (D.finiteGamma A) z = meromorphicOrderAt (E.finiteGamma A) z := by
  have hsum := meromorphicOrderAt_congr (globalFiniteGammaComparison P S D E h z)
  rw [finiteGamma_order_eq_order_sum h.1 (Finset.Subset.refl S) z,
    finiteGamma_order_eq_order_sum h.2.1 (Finset.Subset.refl S) z] at hsum
  have hdiff :
      (∑ v ∈ S \ A, meromorphicOrderAt (D.localFactors v).gamma z) =
      ∑ v ∈ S \ A, meromorphicOrderAt (E.localFactors v).gamma z :=
    Finset.sum_congr rfl fun v hv => haux v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2
  have hD := Finset.sum_sdiff hAS (f := fun v => meromorphicOrderAt (D.localFactors v).gamma z)
  have hE := Finset.sum_sdiff hAS (f := fun v => meromorphicOrderAt (E.localFactors v).gamma z)
  rw [← hD, ← hE, ← hdiff] at hsum
  rw [finiteGamma_order_eq_order_sum h.1 hAS z, finiteGamma_order_eq_order_sum h.2.1 hAS z]
  exact WithTop.add_left_cancel (finiteGamma_order_sum_ne_top h.1 Finset.sdiff_subset z) hsum

/-- Two global comparisons isolate the order at one place. The orders of the
auxiliary factors match on each comparison, and the archimedean product
on each side has the same order in the two comparisons. -/
def TwoTwistGammaOrderMatchingStatement : Prop :=
  ∀ (P : Type u) [DecidableEq P] (S₁ S₂ A : Finset P) (w : P)
    (D₁ E₁ D₂ E₂ : FiniteEulerData P),
    A ⊆ S₁ → insert w A ⊆ S₂ → w ∉ A →
    ComparisonInputs D₁ E₁ S₁ → ComparisonInputs D₂ E₂ S₂ →
    ∀ z : ℂ,
      meromorphicOrderAt (D₁.finiteGamma A) z = meromorphicOrderAt (D₂.finiteGamma A) z →
      meromorphicOrderAt (E₁.finiteGamma A) z = meromorphicOrderAt (E₂.finiteGamma A) z →
      (∀ v ∈ S₁, v ∉ A → meromorphicOrderAt (D₁.localFactors v).gamma z =
        meromorphicOrderAt (E₁.localFactors v).gamma z) →
      (∀ v ∈ S₂, v ∉ insert w A → meromorphicOrderAt (D₂.localFactors v).gamma z =
        meromorphicOrderAt (E₂.localFactors v).gamma z) →
      meromorphicOrderAt (D₂.localFactors w).gamma z =
        meromorphicOrderAt (E₂.localFactors w).gamma z

theorem twoTwistGammaOrderMatching : TwoTwistGammaOrderMatchingStatement.{u} := by
  intro P _ S₁ S₂ A w D₁ E₁ D₂ E₂ hA hAw hw h₁ h₂ z hD hE hAux₁ hAux₂
  have harch := hD.symm.trans ((retained_order_match hA h₁ z hAux₁).trans hE)
  have hblock := retained_order_match hAw h₂ z hAux₂
  have hAS₂ : A ⊆ S₂ := fun v hv => hAw (Finset.mem_insert_of_mem hv)
  rw [finiteGamma_order_eq_order_sum h₂.1 hAw z,
    finiteGamma_order_eq_order_sum h₂.2.1 hAw z, Finset.sum_insert hw, Finset.sum_insert hw,
    ← finiteGamma_order_eq_order_sum h₂.1 hAS₂ z,
    ← finiteGamma_order_eq_order_sum h₂.2.1 hAS₂ z, ← harch] at hblock
  refine WithTop.add_right_cancel ?_ hblock
  rw [finiteGamma_order_eq_order_sum h₂.1 hAS₂ z]
  exact finiteGamma_order_sum_ne_top h₂.1 hAS₂ z

end Langlands.Global.FunctionalEquationComparison
