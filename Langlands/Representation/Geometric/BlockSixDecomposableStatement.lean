import Langlands.Representation.Geometric.GeneralIntersections

/-! Actual block-group specialization of the six BZ77 decomposability conditions. -/

namespace Langlands.Geometric

open GeneralLinear

universe uR

/-- The six literal intersection decompositions for standard block groups and
an arbitrary permutation matrix, over any commutative ring. -/
def BlockParabolicSixDecomposable : Prop :=
  ∀ (R : Type uR) [CommRing R] (n : ℕ) (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)),
    General.SixDecomposable
      (B.parabolic R) (B.leviSubgroup R) (B.unipotentSubgroup R)
      (C.parabolic R) (C.leviSubgroup R) (C.unipotentSubgroup R)
      (GeneralLinear.permutation n R w)

end Langlands.Geometric
