import Langlands.Global.Factors.FiniteComparisonProof
import Mathlib.Algebra.BigOperators.WithTop

/-! # Two-twist isolation of a local gamma order -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.FunctionalEquationComparison

variable {Place : Type u}

private theorem finiteGamma_order_sum {D : FiniteEulerData Place} {S : Finset Place}
    (hD : Admissible D S) (A : Finset Place) (hA : A ⊆ S) (z : ℂ) :
    meromorphicOrderAt (D.finiteGamma A) z =
      ∑ v ∈ A, meromorphicOrderAt (D.localFactors v).gamma z :=
  meromorphicOrderAt_fun_prod fun v hv => (admissible_gamma_nonzero hD v (hA hv)).1 z

private theorem finiteGamma_order_eq_of_order_zero_outside {D : FiniteEulerData Place}
    {S A : Finset Place} (hD : Admissible D S) (hA : A ⊆ S) (z : ℂ)
    (hzero : ∀ v ∈ S, v ∉ A → meromorphicOrderAt (D.localFactors v).gamma z = 0) :
    meromorphicOrderAt (D.finiteGamma S) z = meromorphicOrderAt (D.finiteGamma A) z := by
  rw [finiteGamma_order_sum hD S (Finset.Subset.refl S) z, finiteGamma_order_sum hD A hA z]
  exact (Finset.sum_subset hA hzero).symm

private theorem finiteGamma_order_ne_top {D : FiniteEulerData Place} {S A : Finset Place}
    (hD : Admissible D S) (hA : A ⊆ S) (z : ℂ) :
    meromorphicOrderAt (D.finiteGamma A) z ≠ ⊤ := by
  rw [finiteGamma_order_sum hD A hA z, WithTop.sum_ne_top]
  exact fun v hv => (admissible_gamma_nonzero hD v (hA hv)).2 z

/-- Two global comparisons isolate one local order. The first comparison retains the
archimedean block `A`. The second retains `insert w A`. The exceptional sets
may differ. Orders outside the respective retained blocks must vanish, and the
order of the archimedean product on each side must be preserved between twists. -/
def TwoTwistGammaOrderIsolationStatement : Prop :=
  ∀ (Place : Type u) [DecidableEq Place] (S₁ S₂ A : Finset Place) (w : Place)
    (D₁ E₁ D₂ E₂ : FiniteEulerData Place),
    A ⊆ S₁ → insert w A ⊆ S₂ → w ∉ A →
    ComparisonInputs D₁ E₁ S₁ → ComparisonInputs D₂ E₂ S₂ →
    ∀ z : ℂ,
      meromorphicOrderAt (D₁.finiteGamma A) z = meromorphicOrderAt (D₂.finiteGamma A) z →
      meromorphicOrderAt (E₁.finiteGamma A) z = meromorphicOrderAt (E₂.finiteGamma A) z →
      (∀ v ∈ S₁, v ∉ A →
        meromorphicOrderAt (D₁.localFactors v).gamma z = 0 ∧
        meromorphicOrderAt (E₁.localFactors v).gamma z = 0) →
      (∀ v ∈ S₂, v ∉ insert w A →
        meromorphicOrderAt (D₂.localFactors v).gamma z = 0 ∧
        meromorphicOrderAt (E₂.localFactors v).gamma z = 0) →
      meromorphicOrderAt (D₂.localFactors w).gamma z =
        meromorphicOrderAt (E₂.localFactors w).gamma z

theorem twoTwistGammaOrderIsolation : TwoTwistGammaOrderIsolationStatement.{u} := by
  intro Place _ S₁ S₂ A w D₁ E₁ D₂ E₂ hA hAw hw h₁ h₂ z hD hE hz₁ hz₂
  have harch₁ := meromorphicOrderAt_congr (globalFiniteGammaComparison Place S₁ D₁ E₁ h₁ z)
  rw [finiteGamma_order_eq_of_order_zero_outside h₁.1 hA z (fun v hv ha => (hz₁ v hv ha).1),
    finiteGamma_order_eq_of_order_zero_outside h₁.2.1 hA z (fun v hv ha => (hz₁ v hv ha).2)]
    at harch₁
  have harch₂ := hD.symm.trans (harch₁.trans hE)
  have hblock := meromorphicOrderAt_congr (globalFiniteGammaComparison Place S₂ D₂ E₂ h₂ z)
  rw [finiteGamma_order_eq_of_order_zero_outside h₂.1 hAw z (fun v hv ha => (hz₂ v hv ha).1),
    finiteGamma_order_eq_of_order_zero_outside h₂.2.1 hAw z (fun v hv ha => (hz₂ v hv ha).2),
    finiteGamma_order_sum h₂.1 _ hAw z, finiteGamma_order_sum h₂.2.1 _ hAw z,
    Finset.sum_insert hw, Finset.sum_insert hw] at hblock
  have hAS₂ : A ⊆ S₂ := fun v hv => hAw (Finset.mem_insert_of_mem hv)
  rw [← finiteGamma_order_sum h₂.1 A hAS₂ z, ← finiteGamma_order_sum h₂.2.1 A hAS₂ z,
    ← harch₂] at hblock
  exact WithTop.add_right_cancel (finiteGamma_order_ne_top h₂.1 hAS₂ z) hblock

end Langlands.Global.FunctionalEquationComparison
