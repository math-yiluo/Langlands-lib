import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelProof
import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration

/-! # The connected Néron model of a torus over the maximal unramified field -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme
open Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

private theorem exists_connectedNeronModel :
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp,
      M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
        M.integralPoints = localTorusFiltration F T hT 0 := by
  let L := localTorusSplittingData F T hT
  obtain ⟨M, hSmooth, hConnected, hPoints⟩ :=
    unramifiedTorusIwahoriModel F T L.L L.splits
  exact ⟨M, hSmooth, hConnected,
    hPoints.trans (localTorusFiltration_zero F L.L T hT L.splits).symm⟩

/-- The smooth affine connected model of the norm-defined Iwahori subgroup of `T(K)`. -/
def connectedNeronModel :
    IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp :=
  (exists_connectedNeronModel F T hT).choose

theorem connectedNeronModel_isSmooth : (connectedNeronModel F T hT).IsSmooth :=
  (exists_connectedNeronModel F T hT).choose_spec.1

theorem connectedNeronModel_hasGeometricallyConnectedFibres :
    (connectedNeronModel F T hT).HasGeometricallyConnectedFibres :=
  (exists_connectedNeronModel F T hT).choose_spec.2.1

/-- Its integral points are the Library's actual torus Iwahori subgroup. -/
theorem connectedNeronModel_integralPoints :
    (connectedNeronModel F T hT).integralPoints = localTorusFiltration F T hT 0 :=
  (exists_connectedNeronModel F T hT).choose_spec.2.2

end Langlands.Geometry.Building
