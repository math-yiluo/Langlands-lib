import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Representation.Plancherel.RenardSpecialCompactComparison
import Langlands.Representation.Plancherel.RenardSameCompactLeviComparison

/-! # Actual maximal-compact Cartan comparison under full local availability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.Plancherel.RenardCartan

/-- The actual valuation-chamber Cartan comparison and its same-compact
standard-Levi compatibility for full corrected KP Definition 4.1.26 data.
The only building premise is local availability; every classification,
coverage and finite representative property occurs in the conclusion. -/
def AvailableRenardCartanStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsAvailableFor F G hG →
      let B := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
        ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
          SpecialCompactRenardComparison B.apartment x ν
            B.centralizer.j B.centralizer.s B.centralizer.bijective ∧
          SpecialCompactStandardLeviCompatibility B.apartment x ν
            B.centralizer.s B.centralizer.bijective B.centralizer.j

end Langlands.Plancherel.RenardCartan
