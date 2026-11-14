import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceStatement
import Langlands.Geometry.Building.AffineRootSystem

/-! # Full ordinary derivatives of actual quasi-split apartments -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The ordinary affine roots of every full-V6-compatible quasi-split apartment
have all the actual relative roots as their derivatives. This is an unproved
target over henselian fields with surjective integer-valued valuation. -/
def QuasiSplitDerivativeAffineRootsStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ))),
    Function.Surjective v →
    HenselianLocalRing v.valuationSubring →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsQuasiSplit G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
        letI := mono_of_isMaximalSplitTorus hi
        ∀ (D : KPApartmentData i (IntegerValuation.order v))
          (C : CentralizerDatum i),
          IntegerValuation.IsOmegaCompatible v D C →
          AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i)

end Langlands.Geometry.Building
