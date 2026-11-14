import Langlands.Geometry.Building.UnramifiedSemilinearMetricActionStatement
import Langlands.Geometry.Building.MaximalUnramifiedRootDistance
import Langlands.Geometry.Building.IntegerValuationRetractionDistance
import Langlands.Geometry.Building.RootDistanceMovingAction
import Langlands.Geometry.Building.UnramifiedCoefficientFiniteOrbits

/-! # The complete metric and finite-orbit coefficient action on the unramified building -/

set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance metricActionExtendedAffine
    {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

/-- The exact supplied maximal-unramified quotient has one complete NPC metric,
its existing isometric rational-point action, and a coherent semilinear
isometric coefficient action with finite orbits. -/
theorem unramifiedSemilinearMetricAction :
    UnramifiedSemilinearMetricActionStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let := hG.smooth
  intro C
  let : Fintype (relativeRoots C.i) := C.rootDistanceFintype
  let : NormedAddCommGroup (TranslationSpace C.i) :=
    RootTranslationMetric.normedAddCommGroup C.i
  have hcommon := MaximalUnramified.commonApartments F _ C
  obtain ⟨d, hsmul, hapt, hret⟩ := C.exists_retractionDistance
    (MaximalUnramified.exists_order_eq_one F)
  obtain ⟨m, hdist, hcomplete, hnpc, hgroup⟩ :=
    IntegerValuationBuildingData.exists_metric_of_retractionDistance hcommon hsmul hapt hret
  let := m
  have hd : d = C.invariantRootDistance :=
    C.eq_invariantRootDistance_of_invariant d hsmul hapt
  have hdistroot : ∀ x y : C.ReducedBuilding,
      dist x y = C.apartment.chosenRootDistance hcommon x y := by
    intro x y
    exact (hdist x y).trans (congrFun (congrFun hd x) y)
  have hnorm : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (a b : C.Apartment),
      ‖((MaximalUnramified.coefficientActionData C).apartment σ a -ᵥ
          (MaximalUnramified.coefficientActionData C).apartment σ b : TranslationSpace C.i)‖ =
        ‖(a -ᵥ b : TranslationSpace C.i)‖ := by
    intro σ a b
    exact (MaximalUnramified.coefficientChart C σ).norm_vsub a b
  refine ⟨m, hcomplete, hnpc, hgroup, MaximalUnramified.coefficientAction C,
    MaximalUnramified.coefficientAction_smul C, ?_,
    MaximalUnramified.coefficientAction_finite_range C⟩
  intro σ
  exact C.apartment.movingAction_isometry (MaximalUnramified.coefficientActionData C)
    C.isConnectedReductive C.isMaximalSplitTorus hcommon hnorm hdistroot σ

end Langlands.Geometry.Building
