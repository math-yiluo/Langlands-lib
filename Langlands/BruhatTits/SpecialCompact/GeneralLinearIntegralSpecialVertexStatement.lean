import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.SpecialCompact
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Reductive.GeneralLinearIsConnectedReductiveProof

/-! # The standard integral compact in a valid diagonal building assignment -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building
open scoped ValuativeRel

namespace Langlands.BruhatTits.SpecialCompact

/-- The standard integral points of `GL_N` are the special compact subgroup
of a vertex in the actual diagonal apartment of a valid building assignment. -/
def GeneralLinearIntegralSpecialVertexStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ),
    let G := GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
    let S := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let hG : IsConnectedReductive G := GeneralLinear.isConnectedReductiveStatement F (Fin N)
    haveI := hG.isAffineHom
    ∃ B : KPBuildingAssignment.{u}, B.IsValid ∧
      let V := (B.datum F G hG).base
      V.S = S ∧ HEq V.i i ∧
        ∃ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x ∧
          V.apartment.specialCompactSubgroup x =
            (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints

end Langlands.BruhatTits.SpecialCompact
