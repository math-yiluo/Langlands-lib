import Langlands.Geometry.Building.UnramifiedContainingTorus
import Langlands.Geometry.Building.UnramifiedCentralizingPairApartment
import Langlands.GroupScheme.IntegralModel.ResidueCoefficientMaximalTorus

/-! # Centralizing pair apartments from unit-fixed neutral models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.IntegralModel
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}

local instance unitFixedPairIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unitFixedPairIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unitFixedPairIntegerLocal :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- The actual residue inclusion of the containing torus after unramified
coefficient extension is maximal split. -/
theorem UnitFixedContainingTorusData.unramifiedResidueIsMaximalSplit
    {M : IntegralModel ↥𝒪[F] F G} {iS : S.toGrp ⟶ G}
    (B : UnitFixedContainingTorusData M iS) (hM : M.IsSmooth) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange
        (residueBaseMap (fixedFieldIntegers F))).obj B.unramifiedTorus)
      ((GroupScheme.baseChange
        (residueBaseMap (fixedFieldIntegers F))).map B.unramifiedInclusion) := by
  let : Smooth M.group.X.hom := hM
  exact M.isMaximalSplitTorus_residue_baseChange (A := fixedFieldIntegers F)
    B.inclusion B.residueMaximal B.unramifiedIsSplit

variable [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (iS : S.toGrp ⟶ G) (iT : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (N : RelativeComponentModelData ↥𝒪[F] F G)
  {y₁ y₂ : D.ReducedBuilding}

/-- Unit fixation of the two endpoints, with the exact full-model fixer
equality, suffices for a centralizing pair apartment. -/
def unitFixedPairApartmentOfNeutralModel
    (hfull : N.full.baseChangeUnramified.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {y₁, y₂})
    (hG : IsConnectedReductive G) (hS : IsSplitSubtorus iS)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (f : S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hy₁ : IsFixedByUnramifiedTorusUnits F iS y₁)
    (hy₂ : IsFixedByUnramifiedTorusUnits F iS y₂) :
    {g : rationalPoints (baseChanged F (inertiaFixedField F) G) //
      g ∈ centralizerPoints
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ∧
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        g⁻¹ * rationalConjugate F (inertiaFixedField F) G σ g ∈
          normalizerPoints
            (T := (CommGroupScheme.baseChange
              (algebraBaseMap F (inertiaFixedField F))).obj T)
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) ∧
      (∃ x₁ : D.Apartment, g • D.apartmentMap x₁ = y₁) ∧
      ∃ x₂ : D.Apartment, g • D.apartmentMap x₂ = y₂} := by
  have hY : ∀ y ∈ ({y₁, y₂} : Set D.ReducedBuilding),
      IsFixedByUnramifiedTorusUnits F iS y := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hy₁
    · exact Set.mem_singleton_iff.mp hy ▸ hy₂
  let A := unitFixedNeutralTorusData iS hS N {y₁, y₂} hY
    (le_of_eq hfull.symm)
  let B := unitFixedContainingTorusData N.neutral_smooth A
  exact centralizingPairApartmentOfNeutralTorus iS iT B.genericInclusion D N
    hfull hG hS.1 hiT C hDC f B.sourceHom hf B.source_comm
    B.unramifiedIsSplit B.unramifiedInclusion
    B.unramifiedGenericIso B.unramifiedGeneric_comm
    (B.unramifiedResidueIsMaximalSplit N.neutral_smooth)

end Langlands.Geometry.Building
