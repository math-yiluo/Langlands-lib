import Langlands.BruhatTits.IntegralModels.UnramifiedOpenGeneration
import Langlands.BruhatTits.IntegralModels.FiniteConnectedModelFamily
import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # The actual finite family of unramified root and centralizer models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels.UnramifiedRootCentralizerFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)
    (hN : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))

private instance : Smooth D.full.group.X.hom := D.full_smooth

private abbrev apartmentTorus :=
  unramifiedIntegralSplitTorusData C D.full Ω hN

/-- The centralizer map into the full model, retaining the original
generic centralizer inclusion. -/
def centralizerFullMap :
    (unramifiedNeutralCentralizerModel C D Ω hN).Hom D.full C.centralizer.j := by
  simpa only [Category.comp_id] using
    (unramifiedNeutralCentralizerModelMap C D Ω hN).comp D.inclusion

/-- The optional index selects the actual centralizer or an actual root
representative constructed from the integral apartment torus. -/
def genericGroup : Option (relativeRoots C.i) →
    GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))
  | none => C.centralizer.Z
  | some a => (apartmentTorus C D Ω hN).rootGroup a a.2.1

def model : ∀ j, IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (genericGroup C D Ω hN j)
  | none => unramifiedNeutralCentralizerModel C D Ω hN
  | some a => (apartmentTorus C D Ω hN).rootModel a a.2.1

def genericMap : ∀ j, genericGroup C D Ω hN j ⟶ G
  | none => C.centralizer.j
  | some a => (apartmentTorus C D Ω hN).rootInclusion a a.2.1

def modelMap : ∀ j, (model C D Ω hN j).Hom D.full (genericMap C D Ω hN j)
  | none => centralizerFullMap C D Ω hN
  | some a => (apartmentTorus C D Ω hN).rootModelMap a a.2.1

theorem smooth (j : Option (relativeRoots C.i)) :
    (model C D Ω hN j).IsSmooth := by
  cases j with
  | none => exact unramifiedNeutralCentralizerModel_isSmooth C D Ω hN
  | some a =>
    exact IntegralModel.SplitRoot.model_isSmooth D.full
      (apartmentTorus C D Ω hN).isSplit (apartmentTorus C D Ω hN).inclusion
      ((apartmentTorus C D Ω hN).integralCharacter a)
      ((apartmentTorus C D Ω hN).integralCharacter_ne_zero a.2.1)

theorem geometricallyConnected (j : Option (relativeRoots C.i)) :
    (model C D Ω hN j).HasGeometricallyConnectedFibres := by
  cases j with
  | none => exact unramifiedNeutralCentralizerModel_hasGeometricallyConnectedFibres C D Ω hN
  | some a =>
    exact IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres D.full
      (apartmentTorus C D Ω hN).isSplit (apartmentTorus C D Ω hN).inclusion
      ((apartmentTorus C D Ω hN).integralCharacter a)
      ((apartmentTorus C D Ω hN).integralCharacter_ne_zero a.2.1)

@[instance_reducible] private def indexFintype :
    Fintype (Option (relativeRoots C.i)) := by
  classical
  have := C.isConnectedReductive.smooth
  letI := relativeRootFintypeOfIsSplitTorus C.i C.isMaximalSplitTorus.isSplitSubtorus.1
  infer_instance

private def indexEquiv :
    Fin (@Fintype.card _ (indexFintype C)) ≃ Option (relativeRoots C.i) :=
  (@Fintype.equivFin _ (indexFintype C)).symm

/-- The constructed finite smooth geometrically connected family, with
actual compatible maps into the original full model. -/
def connectedFamily : FiniteConnectedModelFamily D.full where
  size := @Fintype.card _ (indexFintype C)
  genericGroup := fun j => genericGroup C D Ω hN (indexEquiv C j)
  model := fun j => model C D Ω hN (indexEquiv C j)
  smooth := fun j => smooth C D Ω hN (indexEquiv C j)
  geometricallyConnected := fun j => geometricallyConnected C D Ω hN (indexEquiv C j)
  genericMap := fun j => genericMap C D Ω hN (indexEquiv C j)
  modelMap := fun j => modelMap C D Ω hN (indexEquiv C j)

/-- The constructed root model has exactly the actual root-fixer image,
without a boundedness premise. -/
theorem root_integralImage_eq_rootFixer (a : relativeRoots C.i) :
    (model C D Ω hN (some a)).integralPoints.map
        (rationalPoints.map (genericMap C D Ω hN (some a))) =
      C.apartment.rootFixer a Ω := by
  change ((apartmentTorus C D Ω hN).rootModel a a.2.1).integralPoints.map
    (rationalPoints.map ((apartmentTorus C D Ω hN).rootInclusion a a.2.1)) = _
  rw [(apartmentTorus C D Ω hN).rootModel_integralPoints_eq a a.2.1, inf_comm, hN]
  exact C.apartment.rootGroupPoints_inf_oneFixer_eq_rootFixer
    C.isConnectedReductive C.isMaximalSplitTorus (MaximalUnramified.valuation F) a Ω

set_option maxHeartbeats 800000 in
/-- The finite family's integral images generate exactly the actual open
root-centralizer subgroup, with its specified original generic inclusions. -/
theorem integralImages_eq :
    (connectedFamily C D Ω hN).integralImages =
      unramifiedNeutralRootCentralizerGroup C D Ω hN := by
  let U : Option (relativeRoots C.i) → Subgroup (rationalPoints G) :=
    fun j => (model C D Ω hN j).integralPoints.map
      (rationalPoints.map (genericMap C D Ω hN j))
  have henum : (connectedFamily C D Ω hN).integralImages = ⨆ j, U j :=
    (indexEquiv C).iSup_comp (g := U)
  rw [henum, iSup_option]
  change (unramifiedNeutralCentralizerModel C D Ω hN).integralPoints.map
      (rationalPoints.map C.centralizer.j) ⊔
      (⨆ a, (model C D Ω hN (some a)).integralPoints.map
        (rationalPoints.map (genericMap C D Ω hN (some a)))) = _
  unfold unramifiedNeutralRootCentralizerGroup
  congr 1
  exact iSup_congr fun a => root_integralImage_eq_rootFixer C D Ω hN a

/-- Connected generation and finite relative index now suffice: the actual
positive congruence containment is supplied by the proved openness theorem. -/
theorem integralPoints_eq_neutral_of_finiteRelIndex
    (hgen : ConnectedGenerationStatement.{u})
    (hindex : (unramifiedNeutralRootCentralizerGroup C D Ω hN).IsFiniteRelIndex
      D.full.integralPoints) :
    unramifiedNeutralRootCentralizerGroup C D Ω hN = D.neutral.integralPoints := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  rw [← integralImages_eq C D Ω hN]
  apply FiniteConnectedModelFamily.integralImages_eq_neutral hgen D
    (connectedFamily C D Ω hN)
  · rwa [integralImages_eq C D Ω hN]
  · rw [integralImages_eq C D Ω hN]
    exact exists_congruenceSubgroupAt_le_unramifiedNeutralRootCentralizerGroup C D Ω hN

end Langlands.BruhatTits.IntegralModels.UnramifiedRootCentralizerFamily
