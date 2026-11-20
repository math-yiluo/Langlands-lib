import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters

/-! # Arithmetic transport by the norm pullback of a base character -/

noncomputable section

universe uE uE'

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality
open scoped NumberField

/-- Twisting by a norm pullback adds the infinity exponents and preserves
relative regularity. -/
def NormTwistInfinityStatement : Prop :=
  ∀ (E E' : Type uE) [Field E] [NumberField E] [IsTotallyComplex E]
    [Field E'] [NumberField E'] [IsTotallyComplex E'] [Algebra E E']
    (ξ : HeckeCharacter E') (ν : HeckeCharacter E) (a b : ℕ),
    (IsAlgebraicAfterTwist a ξ → IsAlgebraicAfterTwist b ν →
      IsAlgebraicAfterTwist (a + b) (ξ * HeckeCharacter.normComp (L := E') ν)) ∧
    (IsRelativelyRegular E ξ →
      IsRelativelyRegular E (ξ * HeckeCharacter.normComp (L := E') ν))

/-- The actual idele-class norm commutes with arithmetic CM conjugation. -/
def CMNormConjugationStatement : Prop :=
  ∀ (E : Type uE) (E' : Type uE') [Field E] [NumberField E] [IsCMField E]
    [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E']
    (x : IdeleClassGroup (𝓞 E') E'),
    ideleClassNorm (K := E) (L := E') (ideleClassComplexConj x) =
      ideleClassComplexConj (ideleClassNorm (K := E) (L := E') x)

end Langlands.Global.Harris
