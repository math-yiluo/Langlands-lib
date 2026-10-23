import Langlands.Representation.Whittaker.GeneralLinear

/-! Simultaneous finite compact families of equal-rank coefficient and row data. -/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV uW

/-- The two coefficient-model translates and the row-test translate form a
locally constant family with finite range on each compact set. -/
def EqualRankCompactDataStatement (F : Type uF) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] (n : ℕ) : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsSmooth π → IsSmooth σ →
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
      (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      let D := fun g : Langlands.GeneralLinear (n + 1) F =>
        (modelRepresentation π ℓ g f, modelRepresentation σ ℓ' g f',
          fun x : Fin (n + 1) → F => Φ (Matrix.vecMul x g.val))
      IsLocallyConstant D ∧
        ∀ K : Set (Langlands.GeneralLinear (n + 1) F), IsCompact K →
          (Set.range (fun g : K => D g.val)).Finite

end Langlands.RankinSelberg
