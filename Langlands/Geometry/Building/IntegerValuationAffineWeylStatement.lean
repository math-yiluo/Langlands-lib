import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.RankZeroAffineRootSystem

/-! # Affine roots and Weyl reflections for integer-valuation building data

This field-independent target uses the source-positive order and an order-one
unit, and permits the empty affine root system on a point.
-/

universe u

open AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The affine roots of supplied integer-valuation building data form an affine
root system admitting rank zero, and their affine Weyl group is contained in the
actual normalizer image. This is an internal discrete-valuation specialization
of the arguments of KP §§6.2–6.3. -/
def IntegerValuationAffineWeylStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G),
    AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots ∧
      AffineRootSystem.affineWeylGroup B.affineRoots ≤
        B.apartment.normalizerAffineEquiv.range

end Langlands.Geometry.Building
