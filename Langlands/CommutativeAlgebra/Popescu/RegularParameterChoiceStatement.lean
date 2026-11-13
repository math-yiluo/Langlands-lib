import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Choosing regular parameters with annihilator conditions -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.10.2 (07FD): let `Λ` be Noetherian, `I ⊆ q` an ideal and a prime of `Λ` and
`n` such that `qⁿΛ_q ⊆ IΛ_q`, and assume `Λ_q` is a regular local ring. Then for every `e > 0`
there are `π₁, …, π_d ∈ Λ`, with `d` the embedding dimension of `Λ_q`, whose images generate the
maximal ideal of `Λ_q` and form a regular sequence there, such that `πᵢⁿ ∈ I` and
`Ann_{Λ/(π₁ᵉ, …, πᵢ₋₁ᵉ)}(πᵢ) = Ann_{Λ/(π₁ᵉ, …, πᵢ₋₁ᵉ)}(πᵢ²)` for all `i`. -/
def RegularParameterChoiceStatement : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (I q : Ideal Λ) [q.IsPrime] (n : ℕ),
    I ≤ q →
    (q ^ n).map (algebraMap Λ (Localization.AtPrime q)) ≤
      I.map (algebraMap Λ (Localization.AtPrime q)) →
    IsRegularLocalRing (Localization.AtPrime q) →
    ∀ e : ℕ, 0 < e →
      ∃ π : Fin (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank → Λ,
        Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime q)
          (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (π i)) ∧
        (∀ i, π i ^ n ∈ I) ∧
        ∀ (i) (x : Λ), π i ^ 2 * x ∈ Ideal.span ((fun j => π j ^ e) '' {j | j < i}) →
          π i * x ∈ Ideal.span ((fun j => π j ^ e) '' {j | j < i})

end Langlands.CommutativeAlgebra.Popescu
