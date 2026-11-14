import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.GroupScheme.GaloisPointRational
import Langlands.Geometry.Metric.KPDefinitions

/-! # An invariant metric and semilinear action on the unramified building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance semilinearMetricExtendedAffine
    {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

/-- The supplied full-V6 quotient admits a complete NPC metric and a coherent
isometric coefficient action with finite orbits. The actual rational-point
action is isometric and the coefficient action is semilinear for it. -/
def UnramifiedSemilinearMetricActionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G),
      ∃ m : MetricSpace C.ReducedBuilding,
        letI := m
        CompleteSpace C.ReducedBuilding ∧
        Metric.KP.IsNonpositivelyCurved C.ReducedBuilding ∧
        IsIsometricSMul (rationalPoints (baseChanged F (inertiaFixedField F) G))
          C.ReducedBuilding ∧
        ∃ ρ : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →*
            Equiv.Perm C.ReducedBuilding,
          (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
            (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
            (z : C.ReducedBuilding),
            ρ σ (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • ρ σ z) ∧
          (∀ σ, Isometry (ρ σ)) ∧
          ∀ z : C.ReducedBuilding, (Set.range (fun σ => ρ σ z)).Finite

end Langlands.Geometry.Building
