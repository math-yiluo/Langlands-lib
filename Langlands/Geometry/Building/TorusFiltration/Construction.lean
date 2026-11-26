import Langlands.Geometry.Building.TorusFiltration.RightLimit
import Langlands.BruhatTits.IntegralModels.InducedTorusShallowModel
import Langlands.GroupScheme.Dilatation.CongruenceAddition
import Langlands.GroupScheme.Dilatation.StructureProof
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry

/-! # Smooth models and right limits of the minimal congruent torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  (hT : IsTorus T.toGrp)

local notation "K" => inertiaFixedField F
local notation "O" => fixedFieldIntegers F
local notation "κ" => IsLocalRing.ResidueField (fixedFieldIntegers F)
local notation "Model" => IntegralModel O K T.toGrp

private local instance minimalCongruentIntegersDVR : IsDiscreteValuationRing O :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

private def congruenceUniformizer : O :=
  (IsDiscreteValuationRing.exists_irreducible O).choose

private theorem congruenceUniformizer_irreducible : Irreducible (congruenceUniformizer F) :=
  (IsDiscreteValuationRing.exists_irreducible O).choose_spec

include hT in
private theorem torusGeometricallyConnected : GeometricallyConnected T.toGrp.X.hom := by
  let : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  exact Langlands.AlgebraicGeometry.geometricallyConnected_of_connected_section T.toGrp.X.hom
    η[T.toGrp.X].left (Over.w η[T.toGrp.X])

include hT in
private theorem positiveCongruenceGeometry
    (N : Model) (hs : N.IsSmooth) (n : ℕ+) :
    let P := N.positiveCongruenceModel (congruenceUniformizer_irreducible F) n
    P.IsSmooth ∧ P.HasGeometricallyConnectedFibres := by
  have h := IntegralModel.dilatationStructure.2 O K T.toGrp N _
    (congruenceUniformizer_irreducible F) hs n
  rw [N.congruenceModel_coe_pnat] at h
  exact ⟨h.1, h.2.2 (torusGeometricallyConnected F T hT)⟩

local notation "M₀" => connectedNeronModel F T hT

/-- The model at depth `r`, with its smoothness, fibre connectedness and exact integral points. -/
def minimalCongruentModel (r : ℝ≥0) :
    letI : IsAffine T.X.left := Langlands.GroupScheme.SplittingAssembly.isAffine_of_isTorus T.toGrp hT
    {N : Model // N.IsSmooth ∧ N.HasGeometricallyConnectedFibres ∧
      N.integralPoints = minimalCongruentPoints F T hT r} := by
  letI : IsAffine T.X.left := Langlands.GroupScheme.SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  let hπ := congruenceUniformizer_irreducible F
  refine minimalCongruentModelFromDilatation F T hT ?_ ?_ ?_ r
  · intro S hS q hq
    let N := InducedTorusShallow.standardModel F S q hS hq q.property
    exact ⟨N.val, N.property⟩
  · intro H i hi hs hc
    let : IsClosedImmersion i.hom.hom.left := hi
    let : IsAlgClosed κ := (fixedFieldResidueIsAlgClosure F).isAlgClosed
    let : ConnectedSpace H.X.left := hc
    have hCentre := Langlands.AlgebraicGeometry.geometricallyConnected_of_connected_isAlgClosed
      H.X.hom
    have hD := IntegralModel.dilatationStructure.1 O K T.toGrp M₀ _ hπ H i
      (connectedNeronModel_isSmooth F T hT) hs
    exact ⟨(M₀).dilatation hπ i, hD.1, hD.2.2 (torusGeometricallyConnected F T hT) hCentre,
      (M₀).integralPoints_dilatation hπ i⟩
  · intro N n hs _
    have h := positiveCongruenceGeometry F T hT N hs n
    exact ⟨N.positiveCongruenceModel hπ n, h.1, h.2, N.integralPoints_positiveCongruenceModel hπ n⟩

/-- The subgroup at `r+`, whose carrier is the union of terms at depths strictly greater than `r`. -/
def minimalCongruentRightLimit (r : ℝ≥0) :
    letI : IsAffine T.X.left := Langlands.GroupScheme.SplittingAssembly.isAffine_of_isTorus T.toGrp hT
    {Q : Subgroup (rationalPoints T.toGrp) //
      (Q : Set (rationalPoints T.toGrp)) = minimalCongruentPlus F T hT r} := by
  letI : IsAffine T.X.left := Langlands.GroupScheme.SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  let hπ := congruenceUniformizer_irreducible F
  let M₁ := (M₀).positiveCongruenceModel hπ 1
  refine minimalCongruentRightLimitFromCongruence F T hT M₁ ?_ ?_ ?_ r
  · exact (positiveCongruenceGeometry F T hT M₀
      (connectedNeronModel_isSmooth F T hT) 1).1
  · exact ((M₀).integralPoints_positiveCongruenceModel hπ 1).trans (M₀).congruenceSubgroupAt_one
  · intro n
    simpa only [add_comm] using (M₀).congruenceSubgroupAt_positiveCongruenceModel hπ 1 n

end Langlands.Geometry.Building
