import Langlands.Automorphic.HeckeTwist.ContragredientTwist
import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Global.HeckeCharacterTransport

/-! # Conjugate self-duality and supercuspidality under Hecke determinant twists -/

noncomputable section

universe uE uV

namespace Langlands.Automorphic

open Langlands.Global
open NumberField (IsCMField)

/-- A conjugate-inverse Hecke character preserves conjugate self-duality
under the actual determinant twist. -/
def HeckeDeterminantTwistConjugateSelfDualStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (S : OperatorRealization E n) (ν : HeckeCharacter E),
    ν.complexConj = ν⁻¹ → S.IsConjugateSelfDual →
    (S.heckeDeterminantTwist ν).IsConjugateSelfDual

/-- The actual twisted presentation has a supercuspidal component at
each place where the original presentation has one. -/
def HeckeDeterminantTwistSupercuspidalStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [CompactSpace (AdeleQuotient E)]
    {r : ℕ} (S : CuspidalOperatorRealization E r)
    (P : CuspidalSpectralPresentation.{uE, uV} S)
    (ν : HeckeCharacter E) (v : FinitePlace E),
    (P.localComponent v).IsSupercuspidal →
    ((P.heckeDeterminantTwist ν).localComponent v).IsSupercuspidal

end Langlands.Automorphic
