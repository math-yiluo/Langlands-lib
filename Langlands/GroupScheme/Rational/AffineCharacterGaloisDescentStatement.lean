import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.CharacterGaloisAction
import Mathlib.RepresentationTheory.Invariants

/-! # Galois descent of characters of affine group schemes -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For an affine group scheme and a Galois field extension, canonical base change
identifies the rational characters with the invariant characters after extension. -/
def AffineCharacterGaloisDescentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    let extend := (rationalCharacters.baseChange (algebraBaseMap k K) (G := G)).toIntLinearMap
    Function.Injective extend ∧
      LinearMap.range extend = (rationalCharacters.galoisRepresentation k K G).invariants

end Langlands.GroupScheme
