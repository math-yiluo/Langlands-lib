import Langlands.Galois.Local.HarrisLabelledHTFromGradesStatement
import Langlands.Galois.AlgebraicHeckeAvatarStatement

/-! # Tate exponents of the adic avatars of an algebraic Hecke character

At every coefficient place and every label, the avatar of an algebraic Hecke
character of a CM field has a rank-one Tate exponent equal to the exponent of
its infinity type at the corresponding complex embedding. See the paired
Markdown.
-/

noncomputable section

set_option autoImplicit false

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global

/-- The labelled Tate exponent of each avatar of an algebraic Hecke character
`χ` with infinity type `a` is `a(ι ∘ j)` at the label `λ ∘ j`. -/
def AlgebraicHeckeAvatarTateExponentStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [NumberField.IsCMField K]
    (L : Type uL) [Field L] [NumberField L] (ι : L →+* ℂ)
    (χ : HeckeCharacter K) (a : InfinityType K) (S : Finset (FinitePlace K))
    (β : FinitePlace K → Lˣ) (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam),
    χ.HasPrescribedInfinityComponent (InfinityType.toCharacter a) →
    IsUniformHeckeAvatar ι χ S β ψ →
    ∀ (lam : FinitePlace L) (j : K →+* L),
      HasCharacterTateExponentAt lam ((NumberField.FinitePlace.embedding lam).comp j) (ψ lam)
        (a (ι.comp j))

end Langlands.GaloisRepresentation
