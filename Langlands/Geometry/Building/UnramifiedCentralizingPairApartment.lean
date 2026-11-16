import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralPairReference
import Langlands.Geometry.Building.CentralizingIntegralApartment

/-! # Centralizing pair apartments from an actual neutral-model torus -/

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
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S T T' : CommGroupScheme (Spec (CommRingCat.of F))}
  (iS : S.toGrp ⟶ G) (iT : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (N : RelativeComponentModelData ↥𝒪[F] F G)
  {y₁ y₂ : D.ReducedBuilding}

private instance centralizingPairExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

local instance centralizingPairIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance centralizingPairIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- An actual residue-maximal integral torus for a descended generic torus
containing the original split source gives the centralizing pair chart. -/
def centralizingPairApartmentOfNeutralTorus
    (hfull : N.full.baseChangeUnramified.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {y₁, y₂})
    (hG : IsConnectedReductive G) (hS : IsSplitTorus S.toGrp)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (f : S ⟶ T) (f' : S ⟶ T')
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hf' : CommGroupScheme.groupHom f' ≫ j = iS)
    {T₁ : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    (hT₁ : IsSplitTorus T₁.toGrp)
    (i₁ : T₁.toGrp ⟶ N.neutral.baseChangeUnramified.group)
    (e₁ : (CommGroupScheme.baseChange
        (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).obj T₁ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T')
    (he₁ : N.neutral.baseChangeUnramified.genericHom i₁ =
      CommGroupScheme.groupHom e₁.hom ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map j)
    (h₁ : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange
        (residueBaseMap (fixedFieldIntegers F))).obj T₁)
      ((GroupScheme.baseChange (residueBaseMap (fixedFieldIntegers F))).map i₁)) :
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
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let M := N.neutral.baseChangeUnramified
  let E := N.baseChange (fixedFieldIntegers F) (inertiaFixedField F)
  let : GeometricallyConnected M.group.X.hom := E.neutral_geometricallyConnected
  let : ConnectedSpace ((GroupScheme.baseChange
      (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj M.group).X.left :=
    connectedSpace_baseChange_of_geometricallyConnected M.group
      (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  let A := N.neutralPairReference hfull hG hiT C hDC
  let fK := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f
  let f'K := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f'
  have hfK : CommGroupScheme.groupHom fK ≫
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    change (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map
        (CommGroupScheme.groupHom f) ≫ _ = _
    rw [← Functor.map_comp, hf]
  have hf'K : CommGroupScheme.groupHom f'K ≫
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map j =
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    change (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map
        (CommGroupScheme.groupHom f') ≫ _ = _
    rw [← Functor.map_comp, hf']
  let c := D.centralizingConjOfResidueMaximalIntegralTorus F (inertiaFixedField F)
    (R := fixedFieldIntegers F)
    (k := IsLocalRing.ResidueField (fixedFieldIntegers F))
    (Y := {y₁, y₂}) (T₀ := A.torus) (T₁ := T₁)
    iT j M
    (N.neutral.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F)
      N.neutral_smooth)
    (IsLocalRing.residue_surjective (R := fixedFieldIntegers F))
    B.isConnectedReductive
    (hS.baseChange (algebraBaseMap F (inertiaFixedField F)))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
    hiT fK f'K hfK hf'K
    (N.neutral_baseChange_integralPoints_le_fixingSubgroup hfull)
    A.translatingPoint A.subset_range
    A.isSplit hT₁ A.inclusion i₁ A.genericIso A.generic_comm A.isClosed
    e₁ he₁ h₁
  exact ⟨c.val, c.property.1, c.property.2.1,
    c.property.2.2 (by simp), c.property.2.2 (by simp)⟩

end Langlands.Geometry.Building
