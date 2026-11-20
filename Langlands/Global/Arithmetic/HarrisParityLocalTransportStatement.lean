import Langlands.Global.Arithmetic.HarrisProposition48ParityData

/-! # Finite-place transport in the Proposition 4.8 parity correction -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open LocalFactor.CommonClosure GeneralPosition Weil.Local
open scoped NumberField

/-- The norm correction transports an actual component at any compatible place,
and its effect on the Weil character is the restriction of a base Weil character. -/
def Proposition48PlaceNormTwistStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (P : PlaceDatum Q.F Q.F' Q.E Q.E' Q.L)
    (ν : HeckeCharacter Q.E) (η : FieldCharacter Q.F Q.F'),
    NormalizedReciprocity Q.F Q.e → (Q.p : 𝓞 Q.E) ∈ P.v.asIdeal →
    P.IsCompatible → P.HasComponent Q.ξ η →
    ∃ (η' : FieldCharacter Q.F Q.F') (ψ : localWeilGroup Q.F →ₜ* ℂˣ),
      P.HasComponent (Q.correctedCharacter ν) η' ∧
      ∀ w : weilSubgroup Q.F Q.F',
        weilCharacter Q.F Q.e Q.F' η' w = weilCharacter Q.F Q.e Q.F' η w * ψ w.val

/-- An ambient character twist preserves all Mackey constituent irreducibilities
in the same prime cyclic tower. -/
def GeneralPositionAmbientTwistStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (χ χ' : weilSubgroup F F' →ₜ* ℂˣ) (ψ : localWeilGroup F →ₜ* ℂˣ),
    (∀ w : weilSubgroup F F', χ' w = χ w * ψ w.val) →
    IsInGeneralPosition F F' χ → IsInGeneralPosition F F' χ'

end Langlands.Global.Harris
