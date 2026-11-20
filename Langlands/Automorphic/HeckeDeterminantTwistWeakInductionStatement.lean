import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.WeakAutomorphicInduction
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters

/-! # Direct weak induction under the actual Hecke determinant twist -/

noncomputable section

universe uE uV

namespace Langlands.Automorphic

open Langlands.Global

/-- The actual twisted presentation witnesses direct Euler weak induction of
the inducing character multiplied by the norm pullback of the twisting character. -/
def HeckeDeterminantTwistWeakInductionStatement : Prop :=
  ∀ (E E' : Type uE) [Field E] [NumberField E] [Field E'] [NumberField E']
    [Algebra E E'] [CompactSpace (AdeleQuotient E)] {r : ℕ}
    (S : CuspidalOperatorRealization E r) (P : CuspidalSpectralPresentation.{uE, uV} S)
    (ξ : HeckeCharacter E') (ν : HeckeCharacter E),
    P.spectralSystem.IsWeakInductionOf ξ →
    (P.heckeDeterminantTwist ν).spectralSystem.IsWeakInductionOf
      (ξ * HeckeCharacter.normComp (L := E') ν)

end Langlands.Automorphic
