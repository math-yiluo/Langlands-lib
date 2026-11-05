import Langlands.GroupScheme.IntegralModel.MaximalCompactStatement
import Langlands.GroupScheme.IntegralModel.LocalCompactPoints
import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.Geometry.Metric.KPBoundedActionFixedPointProof
import Langlands.Representation.Plancherel.RationalCharacterTopology

/-! # A geometric comparison target for supplied reductive integral models -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.Geometry.Metric.KP

/-- A compact subgroup with continuous orbit maps fixes a point in a nonempty
complete nonpositively curved metric space under an isometric action. -/
theorem exists_fixedPoint_of_isCompact
    {H : Type v} [Group H] [TopologicalSpace H]
    (X : Type w) [MetricSpace X] [CompleteSpace X] [Nonempty X]
    [MulAction H X] [IsIsometricSMul H X]
    (hX : IsNonpositivelyCurved X)
    (horbit : ∀ x : X, Continuous (fun g : H => g • x))
    (L : Subgroup H) (hL : IsCompact (L : Set H)) :
    ∃ x : X, ∀ g : H, g ∈ L → g • x = x := by
  letI : IsIsometricSMul L X := ⟨fun g => isometry_smul X (g : H)⟩
  let x : X := Classical.arbitrary X
  have hcompact : IsCompact ((fun g : H => g • x) '' (L : Set H)) :=
    hL.image (horbit x)
  have horbit_eq :
      (fun g : L => g • x) '' Set.univ =
        (fun g : H => g • x) '' (L : Set H) := by
    ext y
    constructor
    · rintro ⟨g, -, rfl⟩
      exact ⟨g, g.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, Set.mem_univ _, rfl⟩
  have hbounded : HasBoundedAction X (Set.univ : Set L) := by
    refine ⟨x, ?_⟩
    rw [horbit_eq]
    exact hcompact.isBounded
  obtain ⟨y, hy⟩ := boundedActionFixedPoint X hX L hbounded
  exact ⟨y, fun g hg => hy ⟨g, hg⟩⟩

end Langlands.Geometry.Metric.KP

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Geometry.Building
open Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (M : IntegralModel ↥𝒪[F] F G)

private instance genericAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance comparisonGenericTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Geometric data sufficient to identify the actual model image with the
norm-one stabilizer of its unique fixed point in the actual root-valuation
building quotient. Existence of these data is a separate construction target. -/
structure BuildingComparison where
  building : ValuationBuildingData G
  [metric : MetricSpace building.ReducedBuilding]
  [complete : CompleteSpace building.ReducedBuilding]
  nonpositivelyCurved :
    Langlands.Geometry.Metric.KP.IsNonpositivelyCurved building.ReducedBuilding
  [isometric : IsIsometricSMul (rationalPoints G) building.ReducedBuilding]
  continuous_orbit : ∀ x : building.ReducedBuilding,
    Continuous (fun g : rationalPoints G => g • x)
  point : building.ReducedBuilding
  vertex : building.IsVertex point
  special : building.IsSpecialPoint point
  integralPoints_eq : M.integralPoints = building.compactStabilizer point
  unique_fixed : ∀ y : building.ReducedBuilding,
    (∀ g : rationalPoints G, g ∈ M.integralPoints → g • y = y) → y = point

namespace BuildingComparison

variable {M}

/-- The fixed-point argument proves maximality for the supplied model image
whenever the displayed actual-building comparison has been constructed. -/
theorem maximalCompact (D : BuildingComparison M) :
    IsCompact (M.integralPoints : Set (rationalPoints G)) ∧
      ∀ L : Subgroup (rationalPoints G),
        IsCompact (L : Set (rationalPoints G)) → M.integralPoints ≤ L →
          L = M.integralPoints := by
  letI := D.metric
  letI := D.complete
  letI := D.isometric
  letI : Nonempty D.building.ReducedBuilding := ⟨D.point⟩
  refine ⟨M.isCompact_integralPoints_localField, ?_⟩
  intro L hL hML
  obtain ⟨y, hy⟩ := Langlands.Geometry.Metric.KP.exists_fixedPoint_of_isCompact
    D.building.ReducedBuilding D.nonpositivelyCurved D.continuous_orbit L hL
  have hy_eq : y = D.point :=
    D.unique_fixed y (fun g hg => hy g (hML hg))
  have hnorm := compactSubgroup_le_rationalCommonNormKernel G L hL
  apply le_antisymm ?_ hML
  intro g hg
  rw [D.integralPoints_eq]
  apply D.building.mem_compactStabilizer.mpr
  exact ⟨hnorm hg, by simpa only [hy_eq] using hy g hg⟩

end BuildingComparison

/-- An internal construction target for every supplied model with connected
reductive full special fibre. No comparison or metric datum is assumed. -/
def BuildingComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    Nonempty (BuildingComparison M)

/-- Constructing the stated geometric comparison would prove the exact published
maximal-compactness target, without any additional premise in that target. -/
theorem maximalCompactStatement_of_buildingComparison
    (h : BuildingComparisonStatement.{u}) : MaximalCompactStatement.{u} := by
  intro F _ _ _ _ G hG M hspecial
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨D⟩ := h F G hG M hspecial
  exact D.maximalCompact

end Langlands.GroupScheme.IntegralModel
