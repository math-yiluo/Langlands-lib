import Langlands.BaseChange.TwistedCharacter.LaurentComparison
import Langlands.BaseChange.TwistedCharacter.FiniteOrder

/-! # Comparing regular families of twisted distributions -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory Plancherel

universe uX uG uV uW

/-- Two regular families of linear forms related on the unitary torus by `d`-th roots of
unity are related by one `d`-th root of unity on the full torus. -/
def RegularLinearFormComparisonStatement : Prop :=
  ∀ {X : Type uX} [AddCommGroup X] [Module ℂ X] {n d : ℕ}, 0 < d →
    ∀ (F H : (Fin n → ℂˣ) → Module.Dual ℂ X),
      (∀ x, ∃ p : AddMonoidAlgebra ℂ (Fin n → ℤ), ∀ z, F z x = finiteLaurentEvaluation z p) →
      (∀ x, ∃ p : AddMonoidAlgebra ℂ (Fin n → ℤ), ∀ z, H z x = finiteLaurentEvaluation z p) →
      (∀ z : Fin n → Circle, ∃ c : ℂ, c ^ d = 1 ∧
        F (fun i => Circle.toUnits (z i)) = c • H (fun i => Circle.toUnits (z i))) →
      ∃ c : ℂ, c ^ d = 1 ∧ ∀ z, F z = c • H z

/-- Choose Laurent polynomials for each test and use comparison in the Laurent domain. -/
theorem regularLinearFormComparison : RegularLinearFormComparisonStatement.{uX} := by
  intro X _ _ n d hd F H hF hH h
  choose p hp using hF
  choose q hq using hH
  obtain ⟨c, hc, he⟩ := exists_rootOfUnity_laurent_comparison hd p q (fun z => by
    obtain ⟨c, hc, hz⟩ := h z
    refine ⟨c, hc, fun x => ?_⟩
    rw [← hp x, ← hq x]
    exact LinearMap.congr_fun hz x)
  refine ⟨c, hc, fun z => LinearMap.ext fun x => ?_⟩
  simpa only [← hp x, ← hq x, LinearMap.smul_apply, smul_eq_mul] using he z x

section Distributions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- Regular distributions have a single root-of-unity comparison if the unitary
specializations are twisted distributions of equivalent irreducible admissible
representations with normalized operators. The carriers can depend on the specialization. -/
theorem regularTwistedDistributionComparison
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (θ : MulAut G) {n d : ℕ} (hd : 0 < d)
    (F H : (Fin n → ℂˣ) → Distribution G)
    (hF : ∀ f, ∃ p : AddMonoidAlgebra ℂ (Fin n → ℤ), ∀ z, F z f = finiteLaurentEvaluation z p)
    (hH : ∀ f, ∃ p : AddMonoidAlgebra ℂ (Fin n → ℤ), ∀ z, H z f = finiteLaurentEvaluation z p)
    (V : (Fin n → Circle) → Type uV) (W : (Fin n → Circle) → Type uW)
    [∀ z, AddCommGroup (V z)] [∀ z, Module ℂ (V z)]
    [∀ z, AddCommGroup (W z)] [∀ z, Module ℂ (W z)]
    (ρ : ∀ z, Representation ℂ G (V z)) (π : ∀ z, Representation ℂ G (W z))
    (hρ : ∀ z, IsAdmissible (ρ z)) (hπ : ∀ z, IsAdmissible (π z))
    (hirr : ∀ z, (ρ z).IsIrreducible) (e : ∀ z, (ρ z).Equiv (π z))
    (A : ∀ z, (ρ z).Equiv ((ρ z).comp θ.toMonoidHom))
    (B : ∀ z, (π z).Equiv ((π z).comp θ.toMonoidHom))
    (hA : ∀ z, (A z).toLinearMap ^ d = 1) (hB : ∀ z, (B z).toLinearMap ^ d = 1)
    (hFρ : ∀ z, F (fun i => Circle.toUnits (z i)) = twistedDistribution μ (π z) (hπ z)
      (B z).toLinearMap)
    (hHρ : ∀ z, H (fun i => Circle.toUnits (z i)) = twistedDistribution μ (ρ z) (hρ z)
      (A z).toLinearMap) :
    ∃ c : ℂ, c ^ d = 1 ∧ ∀ z, F z = c • H z := by
  apply regularLinearFormComparison hd F H hF hH
  intro z
  rw [hFρ z, hHρ z]
  exact exists_rootOfUnity_twistedDistribution_eq_smul_of_equiv μ θ (hρ z) (hirr z) (hπ z)
    (e z) (A z) (B z) (hA z) (hB z)

end Distributions

end Langlands.BaseChange
