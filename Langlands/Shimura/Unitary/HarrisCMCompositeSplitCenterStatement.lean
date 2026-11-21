import Langlands.Galois.CompatibleFamily
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Shimura.Unitary.FiniteModels

/-! # The oriented split center of Harris's CM composite -/

universe u

set_option autoImplicit false

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global
open Langlands.GaloisRepresentation (residueCharacteristic)
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- The place below `v` in the real field has precisely `v` and its CM
conjugate above it. The split-center coordinates are the actual evaluations
at those places, in that order, after identifying each completion with the
base completion. -/
def HarrisCMCompositeSplitCenterStatement : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] [IsCMField E]
    (E₀ K₀ : IntermediateField ℚ E) [IsTotallyReal E₀],
    E₀ ⊔ K₀ = ⊤ → ∀ v : Langlands.Global.FinitePlace E,
    Harris.IsSplitImaginaryQuadratic (residueCharacteristic v) K₀ →
    ∃ hquad : IsQuadraticExtension E₀ E,
      letI := hquad
      let w := v.under (𝓞 E₀)
      ∃ h₁ : v.asIdeal.LiesOver w.asIdeal,
        letI := h₁
        ∃ h₂ : (Harris.conjPlace E v).asIdeal.LiesOver w.asIdeal,
          letI := h₂
          ∃ (C : SplitPlaceIdentification E₀ E w)
            (e₁ : FiniteCompletion E₀ w ≃ₐ[FiniteCompletion E₀ w] FiniteCompletion E v)
            (e₂ : FiniteCompletion E₀ w ≃ₐ[FiniteCompletion E₀ w]
              FiniteCompletion E (Harris.conjPlace E v)),
            v ≠ Harris.conjPlace E v ∧
              (∀ q : Langlands.Global.FinitePlace E, q.asIdeal.LiesOver w.asIdeal →
                q = v ∨ q = Harris.conjPlace E v) ∧
              (∀ z, e₁ (C.equiv z).1 = completedCenterMap E₀ E w v z) ∧
              (∀ z, e₂ (C.equiv z).2 = completedCenterMap E₀ E w (Harris.conjPlace E v) z)

end Langlands.Shimura.FiniteUnitary
