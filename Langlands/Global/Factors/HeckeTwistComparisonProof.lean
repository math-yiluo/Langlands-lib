import Langlands.Global.Factors.HeckeTwistComparisonStatement
import Langlands.Global.Factors.FiniteComparisonProof

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u

namespace Langlands.Global.FunctionalEquationComparison

/-- The conditional comparison using two actual finite-order Hecke twists. -/
theorem heckeTwistComparison : HeckeTwistComparisonStatement.{u} := by
  classical
  intro hisolate K _ _ T w hw r D E hanalytic hinf hfinite hram hout
  obtain ⟨χ₁, horder₁, _, hinf₁, hdeep₁⟩ :=
    hisolate K ∅ T (Finset.disjoint_empty_left T)
      (fun v => (1 : (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ))
      (fun v => r v.1) (by intro v; exact ⟨1, Nat.zero_lt_one, by simp⟩)
  obtain ⟨χ₂, horder₂, hpres₂, hinf₂, hdeep₂⟩ :=
    hisolate K {w} (T.erase w) (by simp)
      (fun v => (1 : (FiniteCompletion K v.1)ˣ →ₜ* ℂˣ))
      (fun v => r v.1) (by intro v; exact ⟨1, Nat.zero_lt_one, by simp⟩)
  have hw₂ : χ₂.finiteComponent w = 1 := hpres₂ ⟨w, by simp⟩
  have hcharacters : TwoHeckeTwists K T w r χ₁ χ₂ := by
    refine ⟨horder₁, horder₂, hinf₁, hinf₂, hw₂, ?_, ?_⟩
    · intro v hv
      exact hdeep₁ ⟨v, hv⟩
    · intro v hv hvw
      exact hdeep₂ ⟨v, Finset.mem_erase.mpr ⟨hvw, hv⟩⟩
  obtain ⟨B, hTB, hunram, hD₁, hE₁, hD₂, hE₂,
    hfeD₁, hfeE₁, hfeD₂, hfeE₂, σ₁, σ₂,
    hprodD₁, hprodE₁, hmatch₁, hprodD₂, hprodE₂, hmatch₂⟩ :=
    hanalytic χ₁ χ₂ horder₁ horder₂ hinf₁ hinf₂
  have hinputs₁ : ComparisonInputs (D.eulerData χ₁ B) (E.eulerData χ₁ B)
      (exceptionalPlaces K B) :=
    ⟨hD₁, hE₁, hfeD₁, hfeE₁, σ₁, hprodD₁, hprodE₁, hmatch₁⟩
  have hinputs₂ : ComparisonInputs (D.eulerData χ₂ B) (E.eulerData χ₂ B)
      (exceptionalPlaces K B) :=
    ⟨hD₂, hE₂, hfeD₂, hfeE₂, σ₂, hprodD₂, hprodE₂, hmatch₂⟩
  have hAS : archimedeanBlock K ⊆ exceptionalPlaces K B := by
    intro v hv
    cases v <;> simp_all [archimedeanBlock, exceptionalPlaces]
  have hwS : Sum.inr w ∈ exceptionalPlaces K B := by
    simpa [exceptionalPlaces] using hTB hw
  have hwA : Sum.inr w ∉ archimedeanBlock K := by simp [archimedeanBlock]
  have hpres₁D : PreservesGamma (D.eulerData χ₁ B) (D.localFactors 1)
      (archimedeanBlock K) := by
    intro v hv
    cases v with
    | inl v => exact (hinf χ₁ horder₁ hinf₁ v).1
    | inr v => simp [archimedeanBlock] at hv
  have hpres₁E : PreservesGamma (E.eulerData χ₁ B) (E.localFactors 1)
      (archimedeanBlock K) := by
    intro v hv
    cases v with
    | inl v => exact (hinf χ₁ horder₁ hinf₁ v).2
    | inr v => simp [archimedeanBlock] at hv
  have hstable₁ : StableGamma (D.eulerData χ₁ B) (E.eulerData χ₁ B)
      (exceptionalPlaces K B \ archimedeanBlock K) := by
    intro v hv
    cases v with
    | inl v => simp [archimedeanBlock] at hv
    | inr v =>
      by_cases hvT : v ∈ T
      · exact hram v hvT χ₁ horder₁ (hdeep₁ ⟨v, hvT⟩)
      · exact hout χ₁ horder₁ v hvT
  have hpres₂D : PreservesGamma (D.eulerData χ₂ B) (D.localFactors 1)
      (insert (Sum.inr w) (archimedeanBlock K)) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (hfinite χ₂ horder₂ hw₂).1
    · cases v with
      | inl v => exact (hinf χ₂ horder₂ hinf₂ v).1
      | inr v => simp [archimedeanBlock] at hv
  have hpres₂E : PreservesGamma (E.eulerData χ₂ B) (E.localFactors 1)
      (insert (Sum.inr w) (archimedeanBlock K)) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (hfinite χ₂ horder₂ hw₂).2
    · cases v with
      | inl v => exact (hinf χ₂ horder₂ hinf₂ v).2
      | inr v => simp [archimedeanBlock] at hv
  have hstable₂ : StableGamma (D.eulerData χ₂ B) (E.eulerData χ₂ B)
      (exceptionalPlaces K B \ insert (Sum.inr w) (archimedeanBlock K)) := by
    intro v hv
    cases v with
    | inl v => simp [archimedeanBlock] at hv
    | inr v =>
      have hvw : v ≠ w := by
        simpa [archimedeanBlock] using (Finset.mem_sdiff.mp hv).2
      by_cases hvT : v ∈ T
      · exact hram v hvT χ₂ horder₂ (hdeep₂ ⟨v, Finset.mem_erase.mpr ⟨hvw, hvT⟩⟩)
      · exact hout χ₂ horder₂ v hvT
  exact ⟨χ₁, χ₂, B, hcharacters, hTB, hunram,
    twoTwistIsolation (AllPlaces K) (exceptionalPlaces K B) (archimedeanBlock K)
      (.inr w) (D.localFactors 1) (E.localFactors 1)
      (D.eulerData χ₁ B) (E.eulerData χ₁ B) (D.eulerData χ₂ B) (E.eulerData χ₂ B)
      hAS hwS hwA hinputs₁ hinputs₂ hpres₁D hpres₁E hstable₁
      hpres₂D hpres₂E hstable₂⟩

end Langlands.Global.FunctionalEquationComparison
