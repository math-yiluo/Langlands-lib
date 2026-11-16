import Langlands.BruhatTits.IntegralModels.UnramifiedPairApartmentTorus
import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.Geometry.Building.UnramifiedApartmentModelInput
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints
import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Langlands.Geometry.Building.ScalarTorusUnitsFixApartment
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Closed reference tori in the neutral model of a building pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.BruhatTits.IntegralModels

section Reference

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ω : Kˣ → ℝ} (D : KPApartmentData i ω)
  (M : IntegralModel R K G) (y₁ y₂ : D.ReducedBuilding)

/-- A common translated chart and its actual closed integral split torus,
with the original generic identification recorded as an exact equation. -/
structure IntegralPairApartmentReference where
  translatingPoint : rationalPoints G
  firstCoordinate : D.Apartment
  secondCoordinate : D.Apartment
  first_eq : translatingPoint • D.apartmentMap firstCoordinate = y₁
  second_eq : translatingPoint • D.apartmentMap secondCoordinate = y₂
  torus : CommGroupScheme (Spec (CommRingCat.of R))
  isSplit : IsSplitTorus torus.toGrp
  inclusion : torus.toGrp ⟶ M.group
  isClosed : IsClosedSubgroup inclusion
  genericIso : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj torus ≅ S
  generic_comm : M.genericHom inclusion = CommGroupScheme.groupHom genericIso.hom ≫
    (i ≫ (G.innerIso translatingPoint).hom)

/-- The recorded chart covers the actual pair. -/
theorem IntegralPairApartmentReference.subset_range
    (A : IntegralPairApartmentReference D M y₁ y₂) :
    ({y₁, y₂} : Set D.ReducedBuilding) ⊆
      Set.range (fun x : D.Apartment => A.translatingPoint • D.apartmentMap x) := by
  intro y hy
  rcases Set.mem_insert_iff.mp hy with rfl | hy
  · exact ⟨A.firstCoordinate, A.first_eq⟩
  · have he : y = y₂ := Set.mem_singleton_iff.mp hy
    exact ⟨A.secondCoordinate, A.second_eq.trans he.symm⟩

end Reference

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  (B : MaximalUnramified.BuildingData F G)
  (N : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
  (y₁ y₂ : B.ReducedBuilding)

/-- Close the torus of a common apartment in a supplied full pair-fixer
model and factor it through the actual neutral representative. -/
theorem exists_neutralPairApartmentReference
    (hN : characterValuationKernel (MaximalUnramified.valuation F) G ⊓
      B.pointwiseFixer {y₁, y₂} ≤ N.full.integralPoints) :
    Nonempty (IntegralPairApartmentReference B.apartment N.neutral y₁ y₂) := by
  obtain ⟨q, x₁, x₂, hx₁, hx₂⟩ := MaximalUnramified.commonApartments F G B y₁ y₂
  have hY : ({y₁, y₂} : Set B.ReducedBuilding) ⊆
      Set.range (fun x : B.Apartment => q • B.apartmentMap x) := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨x₁, hx₁⟩
    · exact Set.mem_singleton_iff.mp hy ▸ ⟨x₂, hx₂⟩
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  have hv : ∀ a : (fixedFieldIntegers F)ˣ,
      MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)
          (a : fixedFieldIntegers F)) = 1 := by
    intro a
    have h := (Valuation.valuationSubring.integers (fixedFieldValuation F)).valuation_unit a
    have h' := ((MaximalUnramified.valuation_isEquiv F).eq_iff).mpr
      (h.trans (map_one (fixedFieldValuation F)).symm)
    simpa only [map_one] using h'
  have hmax := B.isMaximalSplitTorus.comp_iso (G.innerIso q)
  obtain ⟨T, j, e, hT, hj, hcomm⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      N.full (MaximalUnramified.valuation F) hv (B.i ≫ (G.innerIso q).hom)
      hmax.1.1 hmax.1.2
      ((map_translatedApartmentTorus_kernel_le_oneFixer B q {y₁, y₂} hY).trans hN)
  let : GeometricallyConnected T.toGrp.X.hom := hT.isReductive.geometricallyConnected
  let j₀ := RelativeIdentityComponent.factor j N.isRelativeComponent
  have hj₀ : IsClosedSubgroup j₀ := by
    apply N.isRelativeComponent.isClosedSubgroup_of_comp
    simpa only [j₀, RelativeIdentityComponent.factor_comp] using hj
  refine ⟨⟨q, x₁, x₂, hx₁, hx₂, T, hT, j₀, hj₀, e, ?_⟩⟩
  have hi := N.inclusion.generic_comm
  rw [Category.comp_id] at hi
  change (GroupScheme.baseChange (Spec.algebraMap _ _)).map j₀ ≫
      N.neutral.genericIso.hom = _
  rw [← hi, ← Category.assoc, ← Functor.map_comp,
    RelativeIdentityComponent.factor_comp]
  exact hcomm

/-- Choose the raw closed reference torus and the common chart in the neutral
pair model; the generic square is a field of this construction. -/
def neutralPairApartmentReference
    (hN : characterValuationKernel (MaximalUnramified.valuation F) G ⊓
      B.pointwiseFixer {y₁, y₂} ≤ N.full.integralPoints) :
    IntegralPairApartmentReference B.apartment N.neutral y₁ y₂ :=
  Classical.choice (exists_neutralPairApartmentReference B N y₁ y₂ hN)

end Unramified

section Lower

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))

private instance lowerReferenceExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

local instance neutralPairReferenceIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance neutralPairReferenceIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

namespace RelativeComponentModelData

variable {D} {y₁ y₂ : D.ReducedBuilding}
  (N : RelativeComponentModelData ↥𝒪[F] F G)
  (hfull : N.full.baseChangeUnramified.integralPoints =
    characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {y₁, y₂})

include hfull

/-- The supplied lower neutral model has a closed integral reference torus
for a common chart, after the actual unramified coefficient extension. -/
def neutralPairReference
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C) :
    IntegralPairApartmentReference D N.neutral.baseChangeUnramified y₁ y₂ := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  apply neutralPairApartmentReference B
    (N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)) y₁ y₂
  change characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {y₁, y₂} ≤
    N.full.baseChangeUnramified.integralPoints
  rw [hfull]

/-- Every actual integral point of the supplied lower neutral model fixes
the pair after unramified coefficient extension. -/
theorem neutral_baseChange_integralPoints_le_fixingSubgroup :
    N.neutral.baseChangeUnramified.integralPoints ≤
      fixingSubgroup (rationalPoints (baseChanged F (inertiaFixedField F) G))
        ({y₁, y₂} : Set D.ReducedBuilding) := by
  let E := N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)
  have hle : E.neutral.integralPoints ≤ E.full.integralPoints := by
    rw [← E.neutralPoints_eq]
    exact E.neutralPoints_le_full
  change N.neutral.baseChangeUnramified.integralPoints ≤
    N.full.baseChangeUnramified.integralPoints at hle
  exact hle.trans (by rw [hfull]; exact inf_le_right)

end RelativeComponentModelData
end Lower

end Langlands.BruhatTits.IntegralModels
