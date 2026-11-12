import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.SpecialCompact

/-!
# Special vertices in the apartment of available corrected Bruhat–Tits data

KP Proposition 1.3.43 (1)–(3) for the affine root system of the apartment of data
satisfying the full corrected Definition 4.1.26. This is a statement target conditional
on the available data, not an existence assertion for such data.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- If Bruhat–Tits theory is available for `G` over `F` in `𝔅` (corrected KP Definition
4.1.26), then the reduced apartment `A(S)` of the data of `𝔅` for `G` has a point that is a
special point and a vertex of its affine root system. -/
def AvailableSpecialVertexExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsAvailableFor F G hG →
      let B := (𝔅.datum F G hG).base
      ∃ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x

end Langlands.BruhatTits.SpecialCompact
