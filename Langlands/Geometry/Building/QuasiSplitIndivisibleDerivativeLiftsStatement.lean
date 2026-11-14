import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceStatement
import Langlands.Geometry.Building.AffineTransitiveRootLengths

/-! # Indivisible affine lifts for actual quasi-split apartments -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Every root in the full derivative set of an actual quasi-split apartment
has an indivisible affine lift. The apartment is arbitrary subject to full
integer-valued centralizer compatibility for the prescribed maximal split
torus. This is an unproved target over henselian discretely valued fields. -/
def QuasiSplitIndivisibleDerivativeLiftsStatement : Prop :=
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
          AffineRootSystem.HasIndivisibleDerivativeLifts D.affineRoots

end Langlands.Geometry.Building
