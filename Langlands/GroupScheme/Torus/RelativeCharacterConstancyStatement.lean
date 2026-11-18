import Langlands.GroupScheme.Torus.RelativeMultiplicativeCharacters
import Langlands.AlgebraicGeometry.EtaleLocalSystem

/-! # Statement: constant actual characters detect diagonalizability -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a group of multiplicative type over an arbitrary scheme,
diagonalizability is equivalent to constancy of its actual character
presheaf with a finitely generated abelian coefficient group.
This is the constant-object consequence of the character anti-equivalence
in Conrad (2014), Proposition B.3.4. -/
def RelativeCharacterConstancyStatement : Prop :=
  ∀ (S : Scheme.{u}) (H : GroupScheme S)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H),
    RelativeMultiplicativeType.IsDiagonalizable H ↔
      ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
        Nonempty (hH.characters ≅
          Langlands.AlgebraicGeometry.EtaleLocalSystem.constant S M)

end Langlands.GroupScheme
