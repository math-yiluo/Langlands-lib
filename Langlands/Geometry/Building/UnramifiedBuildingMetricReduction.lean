import Langlands.Geometry.Building.UnramifiedBuildingMetricStatement
import Langlands.Geometry.Building.UnramifiedCompleteNPCMetricStatement
import Langlands.Geometry.Building.IntegerValuationBuildingMetricReduction

/-! # The maximal-unramified building metric from KP Section 4.2 inputs

KP Section 4.2 for the supplied root-valuation quotient over `K = inertiaFixedField F`.
A focused statement isolates the building-theoretic input of KP Proposition 4.2.1 and
Lemma 4.2.2: a `G(K)`-invariant distance extending the Euclidean root distance of the
apartment, with retractions onto the apartment. Together with the published
common-apartment statement it implies `UnramifiedBuildingMetricStatement`; the
reduction is proved here. Discreteness of the normalizer orbits in the apartment (the
apartment step of KP Lemma 4.2.11) is proved here from published results.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building


namespace MaximalUnramified

/-- **Building distance with apartment retractions over `K`** (KP Propositions 4.2.1
and 4.2.3, applied to the root-valuation building of KP Proposition 7.6.3 and
Remark 7.6.5 over the maximal unramified extension `K` of a nonarchimedean local
field `F`). For every supplied building datum over `K`, the reduced building
carries a function `d` which is invariant under `H(K)`, restricts along the
apartment map to the Euclidean root distance of the apartment, and for each
apartment point `a` admits a retraction `ρ` of the building onto the apartment
that fixes the apartment, does not increase distances, and preserves the
distance from `a`. -/
def RetractionDistanceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (B : BuildingData F H),
    ∃ d : B.ReducedBuilding → B.ReducedBuilding → ℝ,
      (∀ (g : rationalPoints H) (x y : B.ReducedBuilding), d (g • x) (g • y) = d x y) ∧
      (∀ a b : B.Apartment,
        d (B.apartmentMap a) (B.apartmentMap b) = B.apartment.rootDistance a b) ∧
      ∀ a : B.Apartment, ∃ ρ : B.ReducedBuilding → B.Apartment,
        (∀ b : B.Apartment, ρ (B.apartmentMap b) = b) ∧
        (∀ x y : B.ReducedBuilding, B.apartment.rootDistance (ρ x) (ρ y) ≤ d x y) ∧
        ∀ x : B.ReducedBuilding, B.apartment.rootDistance a (ρ x) = d (B.apartmentMap a) x

end MaximalUnramified

/-- The published common-apartment statement and the retraction-distance statement of
this module imply `UnramifiedBuildingMetricStatement`. -/
def UnramifiedBuildingMetricReductionStatement : Prop :=
  MaximalUnramified.CommonApartmentsStatement.{u} →
  MaximalUnramified.RetractionDistanceStatement.{u} →
  UnramifiedBuildingMetricStatement.{u}

/-! ### Coefficient isometries of the apartment -/

section RootMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [IsAffineHom (baseChanged k K G).X.hom]
  [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- The coefficient action on a stable apartment preserves the root distance: its
linear part permutes the actual relative roots. -/
theorem rootDistance_galoisAction (σ : K ≃ₐ[k] K) (x y : D.Apartment) :
    D.rootDistance (galoisAction k K i D hD σ x) (galoisAction k K i D hD σ y) =
      D.rootDistance x y := by
  have hv : galoisAction k K i D hD σ x -ᵥ galoisAction k K i D hD σ y =
      galoisTranslationAction k K i σ (x -ᵥ y) :=
    ((galoisAffineAction k K i D hD σ).toAffineMap.linearMap_vsub x y).symm
  rw [rootDistance, rootDistance, hv]
  congr 1
  exact (finsum_comp_equiv (galoisRootAction k K i σ)
    (f := fun α => rootForm _ α (galoisTranslationAction k K i σ (x -ᵥ y)) ^ 2)).symm.trans
    (finsum_congr fun α => by rw [rootForm_galoisTranslationAction])

end KPApartmentData

end RootMetric

/-! ### The reduction -/

private instance unramifiedMetricReductionAffineHom {F : Type u} [Field F] [ValuativeRel F]
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

/-- KP Section 4.2 on the supplied quotient with a coefficient action whose apartment
action preserves the root distance: the glued distance is a metric realization. -/
theorem nonempty_metricRealization_of_retractionDistance
    (hcommon : B.apartment.HasCommonApartments)
    {d : B.ReducedBuilding → B.ReducedBuilding → ℝ}
    (hsmul : ∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
      (x y : B.ReducedBuilding), d (g • x) (g • y) = d x y)
    (hapt : ∀ a b : B.Apartment,
      d (B.apartmentMap a) (B.apartmentMap b) = B.apartment.rootDistance a b)
    (hret : ∀ a : B.Apartment, ∃ ρ : B.ReducedBuilding → B.Apartment,
      (∀ b : B.Apartment, ρ (B.apartmentMap b) = b) ∧
      (∀ x y : B.ReducedBuilding, B.apartment.rootDistance (ρ x) (ρ y) ≤ d x y) ∧
      ∀ x : B.ReducedBuilding, B.apartment.rootDistance a (ρ x) = d (B.apartmentMap a) x)
    (hA : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (a b : B.Apartment),
      B.apartment.rootDistance (A.apartment σ a) (A.apartment σ b) =
        B.apartment.rootDistance a b) :
    Nonempty A.MetricRealization := by
  obtain ⟨_, hdist, _, hnpc, _⟩ :=
    IntegerValuationBuildingData.exists_metric_of_retractionDistance hcommon hsmul hapt hret
  refine ⟨{ nonpositivelyCurved := hnpc, coefficient_isometry := fun σ => ?_ }⟩
  refine Isometry.of_dist_eq fun x y => ?_
  obtain ⟨g, a, b, ha, hb⟩ := hcommon x y
  change g • B.apartmentMap a = x at ha
  change g • B.apartmentMap b = y at hb
  subst ha hb
  rw [action_smul, action_smul, action_apartmentMap, action_apartmentMap, hdist, hdist,
    hsmul, hsmul, hapt, hapt, hA]

end MaximalUnramified.SemilinearApartmentData

/-- The same two inputs give the published `CompleteNPCMetricStatement`, which asks
for the metric on every supplied building datum over `K` without descent data. -/
theorem MaximalUnramified.completeNPCMetricStatement_of_retractionDistance
    (hcommon : MaximalUnramified.CommonApartmentsStatement.{u})
    (hret : MaximalUnramified.RetractionDistanceStatement.{u}) :
    MaximalUnramified.CompleteNPCMetricStatement.{u} := by
  intro F _ _ _ _ H _ B
  obtain ⟨d, hsmul, hapt, hρ⟩ := hret F H B
  obtain ⟨_, -, _, hnpc, _⟩ :=
    IntegerValuationBuildingData.exists_metric_of_retractionDistance (hcommon F H B) hsmul
      hapt hρ
  exact ⟨{ nonpositivelyCurved := hnpc }⟩

set_option maxHeartbeats 1600000 in
/-- KP Section 4.2 for the maximal-unramified building: common apartments and a
retraction distance give a complete NPC metric with isometric rational-point and
coefficient actions. -/
theorem unramifiedBuildingMetricReduction : UnramifiedBuildingMetricReductionStatement.{u} := by
  intro hcommon hret F _ _ _ _ G hG T iT
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD
  obtain ⟨d, hsmul, hapt, hρ⟩ := hret F (baseChanged F (inertiaFixedField F) G)
    (UnramifiedBuildingDescent.buildingData iT
      (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG) hiT D C h6)
  exact MaximalUnramified.SemilinearApartmentData.nonempty_metricRealization_of_retractionDistance
    _ (hcommon F _ _) hsmul hapt hρ
    (KPApartmentData.rootDistance_galoisAction F (inertiaFixedField F) iT D hD)

end Langlands.Geometry.Building
