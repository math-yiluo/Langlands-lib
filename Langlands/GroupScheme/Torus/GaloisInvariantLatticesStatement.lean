import Langlands.GroupScheme.Torus.LatticeBaseInvariants

/-! # Rational characters and cocharacters as Galois invariants -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For any Galois extension, canonical base change identifies the rational
characters and cocharacters of an affine commutative group scheme with the
corresponding invariant lattices after scalar extension. -/
def GaloisInvariantLatticesStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom],
    Function.Bijective (characterLattice.baseChangeToInvariants k K T) ∧
      Function.Bijective (cocharacterLattice.baseChangeToInvariants k K T)

end Langlands.GroupScheme
