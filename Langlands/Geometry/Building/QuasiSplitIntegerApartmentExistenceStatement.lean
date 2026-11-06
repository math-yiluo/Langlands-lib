import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.GroupScheme.Reductive.QuasiSplit
import Mathlib.RingTheory.Henselian

/-! # Actual quasi-split apartments over Henselian discretely valued fields -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Construct an actual normalizer-stable equipollence class of root-datum
valuations, together with its full centralizer compatibility, for every
prescribed maximal split torus of a quasi-split group over a Henselian field
with a surjective integer-valued valuation. This is an existence target, not
a supplied-apartment assumption. -/
def QuasiSplitIntegerApartmentExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ))),
    Function.Surjective v →
    HenselianLocalRing v.valuationSubring →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsQuasiSplit G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
        letI := mono_of_isMaximalSplitTorus hi
        ∃ (D : KPApartmentData i (IntegerValuation.order v))
          (C : CentralizerDatum i),
          IntegerValuation.IsOmegaCompatible v D C

end Langlands.Geometry.Building
