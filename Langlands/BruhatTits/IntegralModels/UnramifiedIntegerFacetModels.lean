import Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelConstruction
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof
import Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof

import Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetRadicalImages
import Langlands.BruhatTits.IntegralModels.IntegerFacetModelMorphisms
import Langlands.Geometry.Building.IntegerValuationChamberBounded
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer

/-! # Constructed actual models and parabolic correspondence on all integer facets -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

private theorem integerFacetModel_torusInputs :
    UnramifiedTorusIwahoriModelStatement.{u} ∧ UnramifiedTorusConnectedBoundStatement.{u} := by
  have hLift : UnramifiedTorusNeutralSurjectivityStatement.{u} :=
    unramifiedTorusNeutralSurjectivityAssembly connectedGeneration torusQuotientRationalSurjectivity
      unramifiedTorusNeutralFiniteGeneration torusSurjectionIsogenySection
  have hBound : UnramifiedTorusConnectedBoundStatement.{u} :=
    unramifiedTorusConnectedBoundAssembly unramifiedTorusBoundedModel hLift
      unramifiedTorusNormPresentation
  have hModel : UnramifiedTorusIwahoriModelStatement.{u} :=
    unramifiedTorusIwahoriModelAssembly IntegralModel.smoothHomExtension
      (unramifiedTorusBoundedModelAssembly maximalBoundedIntegralModel)
      hBound unramifiedTorusIwahoriConnectedImage
  exact ⟨hModel, hBound⟩

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  (E : UnramifiedZeroDatum F G) (C : MaximalUnramified.BuildingData F G)

private local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
private local instance : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
private local instance : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

/-- Every original full integer-building facet has actual smooth full and
neutral models with both exact original generic-point fixer formulas. -/
theorem exists_unramifiedIntegerBuildingFacetModel (J : C.BuildingFacet) :
    ∃ N : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G,
      N.full.integralPoints = characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          C.pointwiseFixer J.val ∧
        N.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val := by
  obtain ⟨g, Fa, hFa, hJ⟩ := J.property
  have hne : Fa.Nonempty := by
    obtain ⟨a, ha⟩ := hFa
    exact ha ▸ ⟨a, AffineRootSystem.mem_facet_self _ _⟩
  have hv : ∃ a : (inertiaFixedField F)ˣ,
      IntegerValuation.order (MaximalUnramified.valuation F) a ≠ 0 := by
    obtain ⟨a, ha⟩ := MaximalUnramified.exists_order_eq_one F
    exact ⟨a, by rw [ha]; exact one_ne_zero⟩
  obtain ⟨hModel, hBound⟩ := integerFacetModel_torusInputs.{u}
  obtain ⟨N, hf, hn⟩ := exists_unramifiedParahoricModel_of_torusInputs hModel hBound
    C E g Fa hne (C.isBoundedApartmentSubset_of_isFacet hv hFa)
  exact ⟨N, by simpa only [hJ] using hf, by simpa only [hJ] using hn⟩

/-- Choose the actual relative component model at each full facet, with its
original generic group and the original zero datum. -/
def unramifiedIntegerBuildingFacetModel (J : C.BuildingFacet) :
    RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G :=
  Classical.choose (exists_unramifiedIntegerBuildingFacetModel E C J)

theorem unramifiedIntegerBuildingFacetModel_full_integralPoints (J : C.BuildingFacet) :
    (unramifiedIntegerBuildingFacetModel E C J).full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓ C.pointwiseFixer J.val :=
  (Classical.choose_spec (exists_unramifiedIntegerBuildingFacetModel E C J)).1

theorem unramifiedIntegerBuildingFacetModel_neutral_integralPoints (J : C.BuildingFacet) :
    (unramifiedIntegerBuildingFacetModel E C J).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer J.val :=
  (Classical.choose_spec (exists_unramifiedIntegerBuildingFacetModel E C J)).2

/-- Actual comparison maps are constructed from full integral-point inclusion;
no family or incidence-map existence is assumed. -/
def unramifiedIntegerFacetModels : IntegerFacetModelData C (fixedFieldIntegers F) :=
  IntegerFacetModelData.ofIntegralPoints C (unramifiedIntegerBuildingFacetModel E C)
    (unramifiedIntegerBuildingFacetModel_full_integralPoints E C)

theorem unramifiedIntegerFacetModels_full_integralPoints (J : C.BuildingFacet) :
    ((unramifiedIntegerFacetModels E C).model J).full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓ C.pointwiseFixer J.val :=
  unramifiedIntegerBuildingFacetModel_full_integralPoints E C J

theorem unramifiedIntegerFacetModels_neutral_integralPoints (J : C.BuildingFacet) :
    ((unramifiedIntegerFacetModels E C).model J).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer J.val :=
  unramifiedIntegerBuildingFacetModel_neutral_integralPoints E C J

/-- The constructed actual family has the original full facet-parabolic order
bijection at every full facet and every valid supplied reductive quotient. -/
theorem unramifiedIntegerFacetModels_hasFacetParabolicOrderBijection
    (J : C.BuildingFacet)
    (Q : SpecialFibreQuotientData ((unramifiedIntegerFacetModels E C).model J))
    (hQ : Q.IsReductiveQuotient) :
    (unramifiedIntegerFacetModels E C).HasFacetParabolicOrderBijection J Q :=
  (unramifiedIntegerFacetModels E C).hasUnramifiedIntegerFacetParabolicOrderBijection_of_zeroFixers
    E C (unramifiedIntegerFacetModels_neutral_integralPoints E C) J Q hQ

/-- Actual full-facet model existence and both fixer formulas, with the full
all-test parabolic correspondence for every valid quotient in the same family. -/
def UnramifiedIntegerFacetModelsStatement : Prop :=
  ∃ M : IntegerFacetModelData C (fixedFieldIntegers F),
    (∀ J : C.BuildingFacet, (M.model J).full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓ C.pointwiseFixer J.val) ∧
    (∀ J : C.BuildingFacet, (M.model J).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer J.val) ∧
    ∀ (J : C.BuildingFacet) (Q : SpecialFibreQuotientData (M.model J)),
      Q.IsReductiveQuotient → M.HasFacetParabolicOrderBijection J Q

theorem unramifiedIntegerFacetModelsStatement : UnramifiedIntegerFacetModelsStatement E C :=
  ⟨unramifiedIntegerFacetModels E C,
    unramifiedIntegerFacetModels_full_integralPoints E C,
    unramifiedIntegerFacetModels_neutral_integralPoints E C,
    unramifiedIntegerFacetModels_hasFacetParabolicOrderBijection E C⟩

end Langlands.BruhatTits.IntegralModels
