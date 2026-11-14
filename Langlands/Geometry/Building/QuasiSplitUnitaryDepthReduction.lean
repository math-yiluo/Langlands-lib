import Langlands.Geometry.Building.UnitaryIndivisibleAffineLifts
import Langlands.Geometry.Building.QuasiSplitIndivisibleDerivativeLiftsStatement
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Reduction of actual quasi-split lifts to multipliable unitary depths -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {j : Z ⟶ G} {s : S.toGrp ⟶ Z}
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData i (IntegerValuation.order v))

/-- For an actual maximal split torus of a connected reductive group,
opposite-factor existence supplies the missing no-quadruple-root condition. -/
theorem hasIndivisibleDerivativeLifts_of_isMaximalSplitTorus_unitaryTowerDepths
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hH : HenselianLocalRing v.valuationSubring) (hv : Function.Surjective v)
    (hc : D.HasMultipliableUnitaryTowerDepths (j := j) (s := s) hH) :
    AffineRootSystem.HasIndivisibleDerivativeLifts D.affineRoots := by
  let : Smooth G.X.hom := hG.smooth
  have hF : RelativeRoot.HasOppositeFactorPairs i := by
    intro a ha g hg hg1
    exact ((rootRankOneFactorization k G hG S i hi) a ha g hg hg1).1.exists
  exact D.hasIndivisibleDerivativeLifts_of_unitaryTowerDepths hH hv hi.1.1
    (no_quadruple_root_of_oppositePairs hi.1.1 hF) hc

end KPApartmentData

/-- The remaining coordinate-and-depth existence premise with precisely the
field, group, torus, apartment and centralizer scope of the published lift target. -/
def QuasiSplitMultipliableUnitaryTowerDepthsStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ))),
    Function.Surjective v →
    ∀ (hH : HenselianLocalRing v.valuationSubring)
      (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsQuasiSplit G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
        letI := mono_of_isMaximalSplitTorus hi
        ∀ (D : KPApartmentData i (IntegerValuation.order v))
          (C : CentralizerDatum i),
          IntegerValuation.IsOmegaCompatible v D C →
          D.HasMultipliableUnitaryTowerDepths (j := C.j) (s := C.s) hH

/-- Exact-target reduction; the multipliable unitary depth existence premise
is retained explicitly and is not proved by this implication. -/
theorem quasiSplitIndivisibleDerivativeLifts_of_multipliableUnitaryTowerDepths
    (hc : QuasiSplitMultipliableUnitaryTowerDepthsStatement.{u}) :
    QuasiSplitIndivisibleDerivativeLiftsStatement.{u} := by
  intro k _ v hv hH G _ hq S i hi
  let := mono_of_isMaximalSplitTorus hi
  intro D C hD
  exact D.hasIndivisibleDerivativeLifts_of_isMaximalSplitTorus_unitaryTowerDepths
    hq.isConnectedReductive hi hH hv (hc k v hv hH G hq S i hi D C hD)

end Langlands.Geometry.Building
