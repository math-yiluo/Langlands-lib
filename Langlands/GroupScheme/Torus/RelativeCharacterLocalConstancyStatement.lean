import Langlands.GroupScheme.Torus.RelativeMultiplicativeCharacters
import Langlands.AlgebraicGeometry.EtaleLocalSystem

/-! # Statement: actual relative characters are an abelian étale local system -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual relative character presheaf of a group of multiplicative type
is an étale locally constant sheaf of finitely generated abelian groups.
This is the character-sheaf assertion of Conrad (2014), Proposition B.3.4,
on the big relative site with its actual pullback restriction maps. -/
def RelativeCharacterLocalConstancyStatement : Prop :=
  ∀ (S : Scheme.{u}) (H : GroupScheme S)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H),
    Langlands.AlgebraicGeometry.EtaleLocalSystem.IsFinitelyGeneratedLocallyConstant.{u, u}
      hH.characters

end Langlands.GroupScheme
