import Langlands.AbelianScheme.NeronModel

/-! # Existence of an abelian variety's Néron model over a DVR -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- An abelian variety over the fraction field of a discrete valuation ring
admits a commutative Néron model with its generic fibre identified with the
original variety. -/
def NeronModelExistenceStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (B : AbelianScheme (Spec (CommRingCat.of K))), Nonempty (NeronModel V K B)

end Langlands.AbelianScheme
