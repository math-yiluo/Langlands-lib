import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Specialization of a specified ample line bundle over a DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- On an actual abelian scheme over a discrete valuation domain, a specified
total line bundle that is ample on the residue-field fibre at the generic
point is ample on the residue-field fibre at the closed point. -/
def DvrAbelianAmpleSpecializationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))
    (L : LineBundle A.X.left),
    ((LineBundle.pullback
      (A.X.hom.fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R))).obj L).IsAmple →
      ((LineBundle.pullback
        (A.X.hom.fiberι (IsLocalRing.closedPoint R))).obj L).IsAmple

end Langlands.AlgebraicGeometry.Picard
