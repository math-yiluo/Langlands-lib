import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.Geometry.Metric.KPDefinitions

/-! # Complete NPC metrics for the maximal-unramified building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedMetricAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

namespace MaximalUnramified.SemilinearApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (A : MaximalUnramified.SemilinearApartmentData B)

/-- A complete NPC metric on the original reduced building, with the original
rational-point action and coefficient action both isometric. No normalization,
comparison topology, or continuity condition is prescribed. -/
structure MetricRealization where
  [metric : MetricSpace B.ReducedBuilding]
  [complete : CompleteSpace B.ReducedBuilding]
  nonpositivelyCurved : Langlands.Geometry.Metric.KP.IsNonpositivelyCurved B.ReducedBuilding
  [isometric : IsIsometricSMul
    (rationalPoints (baseChanged F (inertiaFixedField F) G)) B.ReducedBuilding]
  coefficient_isometry : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    Isometry (A.action σ)

end MaximalUnramified.SemilinearApartmentData

/-- The metric consequence of KP Section 4.2 and the root-valuation construction
of Section 7.6 for the supplied maximal-unramified building, with a coefficient-
invariant choice of apartment metric as in Sections 7.9 and 9.2. Existence is
asserted on the same quotient and does not assume a metric as input. -/
def UnramifiedBuildingMetricStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D),
        Nonempty (UnramifiedBuildingDescent.semilinearData iT
          (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
          hiT C h6 hD).MetricRealization

end Langlands.Geometry.Building
