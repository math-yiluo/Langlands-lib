import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.TorusFiltration.Points

/-! # Moy–Prasad groups over the maximal unramified field with minimal congruent torus terms -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hT : IsTorus B.centralizer.Z)

/-- `T(K)ᵐᶜ_r` for the torus centralizer of the maximal split torus of `H`. -/
def minimalCongruentTorusFiltration (r : ℝ≥0) : Subgroup (rationalPoints B.centralizer.Z) :=
  minimalCongruentPoints F (B.centralizerTorus hT) hT r

/-- KP Definition 7.3.3 at the constant function `r`, using the minimal congruent
filtration for the torus term. Applied to `H = Z_K`, this is `Z(K)_{x,r}` of KP §9.8. -/
def minimalCongruentMoyPrasad (x : B.Apartment) (r : ℝ≥0) : Subgroup (rationalPoints H) :=
  B.moyPrasadWith (B.minimalCongruentTorusFiltration hT) x r

/-- The two torus terms at zero are the rational points of the connected Néron model. -/
theorem minimalCongruentTorusFiltration_zero :
    B.minimalCongruentTorusFiltration hT 0 = B.centralizerTorusFiltration hT 0 :=
  (minimalCongruentPoints_zero F (B.centralizerTorus hT) hT).trans
    (connectedNeronModel_integralPoints F (B.centralizerTorus hT) hT)

/-- Both choices of torus filtration give the same subgroup at depth zero. -/
theorem minimalCongruentMoyPrasad_zero (x : B.Apartment) :
    B.minimalCongruentMoyPrasad hT x 0 = B.moyPrasad hT x 0 := by
  change (B.minimalCongruentTorusFiltration hT 0).map (rationalPoints.map B.centralizer.j) ⊔ _ =
    (B.centralizerTorusFiltration hT 0).map (rationalPoints.map B.centralizer.j) ⊔ _
  rw [B.minimalCongruentTorusFiltration_zero hT]

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
