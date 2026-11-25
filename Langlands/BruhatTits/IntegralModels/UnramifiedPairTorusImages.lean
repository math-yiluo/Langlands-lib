import Langlands.BruhatTits.IntegralModels.UnramifiedPairApartmentTorus
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralRoots
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.CoefficientSpecialFibreTorus
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.IntegralModel.ResidueSplitTorusGenericLift
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximal
import Langlands.Geometry.Building.SpecialTorusIntegralModelReduction

/-! # Original-residue maximal-torus images from full pair-fixer models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.BruhatTits.IntegralModels

private def pairTorusGroupIso {B : Scheme.{u}} {S T : CommGroupScheme B}
    (e : S ≅ T) : S.toGrp ≅ T.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id

section IntegralUnits

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} {N : IntegralModel R K G}

/-- A closed integral split torus with its actual generic identification
places all units of the prescribed generic source inside the model. -/
theorem IntegralSplitTorusData.map_characterValuationKernel_le_integralPoints
    (A : IntegralSplitTorusData N i)
    {v : Valuation K (WithZero (Multiplicative ℤ))}
    (hv : ∀ c : K, v c ≤ 1 ↔ c ∈ (algebraMap R K).range)
    (hA : IsClosedSubgroup A.inclusion) :
    (characterValuationKernel v S.toGrp).map (rationalPoints.map i) ≤
      N.integralPoints := by
  rintro _ ⟨t, ht, rfl⟩
  let e := pairTorusGroupIso A.genericIso
  have ht' : rationalPoints.map e.inv t ∈
      characterValuationKernel v
        ((GroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus.toGrp) :=
    map_characterValuationKernel_le v e.inv ⟨t, ht, rfl⟩
  have h := N.map_genericHom_mem_integralPoints_of_split_characterKernel
    hv A.isSplit A.inclusion hA (rationalPoints.map e.inv t) ht'
  rw [A.generic_comm, rationalPoints.map_comp_apply] at h
  change rationalPoints.map i (rationalPoints.map e.hom (rationalPoints.map e.inv t)) ∈
    N.integralPoints at h
  have hc : rationalPoints.map e.hom (rationalPoints.map e.inv t) = t := by
    rw [← rationalPoints.map_comp_apply, e.inv_hom_id]
    simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
  rwa [hc] at h

end IntegralUnits

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance pairImagesIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance pairImagesIntegerTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance pairImagesIntegerLocalHom : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  integerToFixedField_isLocalHom F

local instance pairImagesIntegerHenselian : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

local instance pairImagesResidueAlgebra : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

local instance pairImagesResidueAlgClosed : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).isAlgClosed

local instance pairImagesIntegerDVR : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

local instance pairImagesExtendedValuativeRel : ValuativeRel (inertiaFixedField F) :=
  ValuativeRel.ofValuation (fixedFieldValued F).v

local instance pairExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (D : RelativeComponentModelData ↥𝒪[F] F G)
  (y₁ y₂ : B.ReducedBuilding)
  (hfull : characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G) ⊓ B.pointwiseFixer {y₁, y₂} ≤
    D.full.baseChangeUnramified.integralPoints)

include hfull

/-- A full pair-fixer bound constructs a maximal split generic torus whose
units lie in the actual neutral model, by factoring its connected integral
split torus through the relative identity component. -/
theorem exists_maximalSplitTorus_units_le_unramifiedNeutral :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
      (i : T.toGrp ⟶ baseChanged F (inertiaFixedField F) G),
      IsMaximalSplitTorus i ∧
        (characterValuationKernel (MaximalUnramified.valuation F) T.toGrp).map
          (rationalPoints.map i) ≤ D.neutral.baseChangeUnramified.integralPoints := by
  obtain ⟨A⟩ := exists_pairApartmentTorusData B
    D.full.baseChangeUnramified y₁ y₂ hfull
  let E := D.baseChange (fixedFieldIntegers F) (inertiaFixedField F)
  let A₀ := A.integralTorus.factorNeutral E
  refine ⟨B.S, B.i ≫ ((baseChanged F (inertiaFixedField F) G).innerIso
    A.translatingPoint).hom, A.generic_isMaximalSplitTorus, ?_⟩
  exact A₀.map_characterValuationKernel_le_integralPoints
    (MaximalUnramified.valuation_le_one_iff_mem_range (F := F))
    (A.integralTorus.factorNeutral_isClosedSubgroup E A.isClosed)

variable {N : IntegralModel ↥𝒪[F] F G} [Smooth N.group.X.hom]
  (φ : D.neutral.Hom N (𝟙 G))

/-- A full pair-fixer source suffices for preservation of every maximal torus
over the original residue field through an actual neutral-model comparison. -/
theorem isMaximalTorus_specialFibreMap_of_unramified_full_pair
    {T : CommGroupScheme (Spec (CommRingCat.of 𝓀[F]))}
    {i : T.toGrp ⟶ D.neutral.specialFibre} (hi : IsMaximalTorus i) :
    IsMaximalTorus (i ≫ φ.specialFibreMap) := by
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  let : ConnectedSpace D.neutral.specialFibre.X.left :=
    D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres
  obtain ⟨T₀, i₀, hi₀, hb⟩ :=
    exists_maximalSplitTorus_units_le_unramifiedNeutral B D y₁ y₂ hfull
  have heq : (ValuativeRel.valuation (inertiaFixedField F)).IsEquiv
      (MaximalUnramified.valuation F) := by
    intro x y
    change _ ≤ _ ↔ MaximalUnramified.valueGroupEquiv F _ ≤
      MaximalUnramified.valueGroupEquiv F _
    rw [map_le_map_iff]
    exact Iff.rfl
  rw [← characterValuationKernel_eq_of_isEquiv heq T₀.toGrp] at hb
  exact φ.isMaximalTorus_specialFibreMap_of_coefficient_bounded
    (A := fixedFieldIntegers F) (L := inertiaFixedField F)
    B.isConnectedReductive (ValuativeRel.valuation (inertiaFixedField F))
    (fun a => heq.eq_one_iff_eq_one.mpr
      (SpecialTorusIntegralModel.valuation_units_eq_one F a)) hi₀ hb hi

namespace RelativeComponentModelHom

variable {D₁ : RelativeComponentModelData ↥𝒪[F] F G}
  (ψ : RelativeComponentModelHom D D₁)
  (Q : SpecialFibreQuotientData D₁) (hQ : Q.IsReductiveQuotient)

include hQ

/-- Every original-residue maximal torus remains maximal after the actual
neutral comparison and the target's valid reductive-quotient projection. -/
theorem isMaximalTorus_quotientMap_of_unramified_full_pair
    {T : CommGroupScheme (Spec (CommRingCat.of 𝓀[F]))}
    {i : T.toGrp ⟶ D.neutral.specialFibre} (hi : IsMaximalTorus i) :
    IsMaximalTorus (i ≫ ψ.neutralSpecialFibreMap ≫ Q.projection) := by
  let : Smooth D₁.neutral.group.X.hom := D₁.neutral_smooth
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffineHom D₁.neutral.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd D₁.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  let : LocallyOfFiniteType D₁.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType (pullback.snd D₁.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  have hm := isMaximalTorus_specialFibreMap_of_unramified_full_pair
    B D y₁ y₂ hfull ψ.neutral hi
  simpa only [Category.assoc] using
    hm.comp_of_perfect_field_unipotent_kernel Q.radicalInclusion
      hQ.1.isClosedSubgroup hQ.1.isUnipotent Q.projection hQ.2.1

end RelativeComponentModelHom

end Unramified

/-- A full pair-fixer bound constructs neutral bounded maximal-split-torus
data and preserves every original-residue maximal torus through any supplied
actual neutral comparison and valid target reductive quotient. -/
def UnramifiedPairTorusImagesStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (D : RelativeComponentModelData ↥𝒪[F] F G) (y₁ y₂ : B.ReducedBuilding),
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓ B.pointwiseFixer {y₁, y₂} ≤
      D.full.baseChangeUnramified.integralPoints →
    (∃ (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
      (i : T.toGrp ⟶ baseChanged F (inertiaFixedField F) G),
      IsMaximalSplitTorus i ∧
        (characterValuationKernel (MaximalUnramified.valuation F) T.toGrp).map
          (rationalPoints.map i) ≤ D.neutral.baseChangeUnramified.integralPoints) ∧
    (∀ (E : RelativeComponentModelData ↥𝒪[F] F G)
      (ψ : RelativeComponentModelHom D E) (Q : SpecialFibreQuotientData E),
      Q.IsReductiveQuotient →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of 𝓀[F])))
        (i : T.toGrp ⟶ D.neutral.specialFibre),
        IsMaximalTorus i →
          IsMaximalTorus (i ≫ ψ.neutralSpecialFibreMap) ∧
          IsMaximalTorus (i ≫ ψ.neutralSpecialFibreMap ≫ Q.projection))

/-- Construct the pair apartment torus in the full model, factor it through
the neutral model, and apply coefficient comparison and unipotent quotients. -/
theorem unramifiedPairTorusImages : UnramifiedPairTorusImagesStatement.{u} := by
  intro F _ _ _ _ G _ B D y₁ y₂ hfull
  refine ⟨exists_maximalSplitTorus_units_le_unramifiedNeutral B D y₁ y₂ hfull, ?_⟩
  intro E ψ Q hQ T i hi
  let : Smooth E.neutral.group.X.hom := E.neutral_smooth
  exact ⟨isMaximalTorus_specialFibreMap_of_unramified_full_pair
      B D y₁ y₂ hfull ψ.neutral hi,
    ψ.isMaximalTorus_quotientMap_of_unramified_full_pair
      B D y₁ y₂ hfull Q hQ hi⟩

end Langlands.BruhatTits.IntegralModels
