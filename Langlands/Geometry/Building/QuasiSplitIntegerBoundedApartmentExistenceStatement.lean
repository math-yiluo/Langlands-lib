import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Mathlib.RingTheory.Henselian

/-! # Bounded quasi-split apartments over henselian discretely valued fields -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private instance boundedApartmentAffine {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Construct a full V 6-compatible apartment class with algebraically bounded
depth-zero root filtrations for every prescribed maximal split torus of a
quasi-split group over a henselian discretely valued field. -/
def QuasiSplitIntegerBoundedApartmentExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [Valuation.Compatible v],
    Function.Surjective v →
    HenselianLocalRing v.valuationSubring →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsQuasiSplit G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
        letI := mono_of_isMaximalSplitTorus hi
        ∃ (D : KPApartmentData i (IntegerValuation.order v))
          (C : CentralizerDatum i),
          IntegerValuation.IsOmegaCompatible v D C ∧
            ∀ (x : D.Apartment) a, a ∈ relativeRoots i →
              IsAlgebraicallyBounded k G.X
                (D.filtration x a 0 : Set (rationalPoints G))

end Langlands.Geometry.Building
