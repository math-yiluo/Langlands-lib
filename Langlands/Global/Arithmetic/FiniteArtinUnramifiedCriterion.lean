import Langlands.Global.Arithmetic.ClassFieldStatement

/-! # The local-unit direction of the finite Artin ramification criterion -/

noncomputable section

universe uK uE

namespace Langlands.Global

/-- The direction of the inertia comparison used at a finite character
kernel. If a normalized map kills the local units, every prime above that
place is unramified in the associated class field. -/
def FiniteArtinUnramifiedCriterionStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K]
    (E : Type uE) [Field E] [NumberField E] [Algebra K E] [IsGalois K E],
    (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) →
    letI : TopologicalSpace (E ≃ₐ[K] E) := ⊥
    ∀ (ρ : IdeleClasses K →ₜ* (E ≃ₐ[K] E)),
      Function.Surjective ρ → HasArithmeticArtinNormalization ρ.toMonoidHom →
      ∀ v : FinitePlace K,
        (∀ a : (FiniteCompletion K v)ˣ,
          a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units →
          ρ (finiteClassInclusion K v a) = 1) →
        ∀ w : FinitePlace E, w.asIdeal.LiesOver v.asIdeal →
          Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) w.asIdeal

end Langlands.Global
