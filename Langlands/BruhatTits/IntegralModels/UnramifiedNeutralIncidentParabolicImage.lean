import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralIncidentDynamicImage
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralCentralizerImage
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentGenericity
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.Absolute.RadicalDynamicParabolicRecognition

/-! # Dynamic parabolics in actual neutral incident comparison images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (M M' : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω Ω' : Set C.Apartment)
    (hM : M.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    (hM' : M'.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω'))
    (ψ : M'.neutral.Hom M.neutral (𝟙 G))
    {Fa Ca : Set C.Apartment}
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
    (hΩ : Ω.Nonempty) (hΩ' : Ω'.Nonempty)
    (hsub : Ω ⊆ Fa) (hsub' : Ω' ⊆ Ca)

local notation "A" => unramifiedNeutralSplitTorusData C M Ω hM
local notation "νs" =>
  IntegralSplitTorusData.cocharacterSpecialization
    (unramifiedNeutralSplitTorusData C M Ω hM)
    (C.incidentFacetCocharacter hCa hFaCa)
local notation "χs" => CommGroupScheme.groupHom νs ≫
  IntegralSplitTorusData.specialFibreInclusion
    (unramifiedNeutralSplitTorusData C M Ω hM)

private instance neutralParabolic_model_smooth
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    Smooth D.neutral.group.X.hom :=
  D.neutral_smooth

private instance neutralParabolic_specialFibre_affine
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

private instance neutralParabolic_specialFibre_smooth
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    Smooth D.neutral.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth D.neutral.group.X.hom))

private instance neutralParabolic_specialFibre_connected
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

/-- The incident cocharacter is generic for the actual neutral residue fibre. -/
theorem unramifiedNeutralIncidentCocharacter_specialization_isGeneric :
    IsGenericCocharacter (A).specialFibreInclusion νs :=
  ((A).isGenericCocharacter_cocharacterSpecialization_iff _).mpr
    (C.incidentFacetCocharacter_isGeneric hCa hFaCa)

/-- Its centralizer is the full residue-torus centralizer on every scheme test. -/
theorem unramifiedNeutralIncidentCocharacter_centralizer_eq_torusCentralizer :
    Dynamic.centralizer χs = torusCentralizer (A).specialFibreInclusion :=
  (A).specialFibreTorus_isSplit.dynamicCentralizer_eq_torusCentralizer
    (A).specialFibreInclusion νs
    (unramifiedNeutralIncidentCocharacter_specialization_isGeneric C M Ω hM hCa hFaCa)

include hM' hΩ hΩ' hsub hsub' in
/-- The full incident dynamic parabolic lies in the actual neutral comparison
image on every residue-scheme test. -/
theorem unramifiedNeutralIncidentDynamicParabolic_le_image :
    Dynamic.parabolic χs ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) := by
  apply parabolic_le_of_torusCentralizer_le_of_unipotent_le
    (A).specialFibreTorus_isSplit (A).specialFibreInclusion νs
    (unramifiedNeutralIncidentCocharacter_specialization_isGeneric C M Ω hM hCa hFaCa)
  · exact unramifiedNeutral_specialCentralizer_le_image C M M' Ω Ω' hM hM' ψ hΩ
  · exact unramifiedNeutralIncidentDynamicUnipotent_le_image
      C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub'

/-- Include incident dynamic-parabolic points in the actual comparison image,
with the same ambient residue-test point. -/
def unramifiedNeutralIncidentDynamicParabolicImagePoints
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))) :
    (Dynamic.parabolic χs).carrier T →*
      (SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap)).carrier T :=
  Subgroup.inclusion ((unramifiedNeutralIncidentDynamicParabolic_le_image
    C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub') T)

@[simp]
theorem unramifiedNeutralIncidentDynamicParabolicImagePoints_val
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (x : (Dynamic.parabolic χs).carrier T) :
    (unramifiedNeutralIncidentDynamicParabolicImagePoints
      C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub' T x).val = x.val :=
  rfl

local instance neutralParabolic_residue_algClosed :
    IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

include hM hM' hCa hFaCa hΩ hΩ' hsub hsub' in
/-- Full radical containment is a sufficient remaining input for parabolicity
of the actual neutral incident comparison image. -/
theorem unramifiedNeutralIncidentImage_isParabolic_of_radical_le
    {U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (r : U ⟶ M.neutral.specialFibre) (hr : IsUnipotentRadical r)
    (hrad : SubgroupFunctor.range r ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap)) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) := by
  let : GeometricallyReduced M'.neutral.specialFibre.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  let : Smooth (SchematicImage.image ψ.specialFibreMap).X.hom :=
    HomImage.smooth_image ψ.specialFibreMap
  exact isParabolicSubgroup_of_dynamic_le_of_radical_le
    r hr (SchematicImage.inclusion ψ.specialFibreMap)
    (HomImage.isClosedSubgroup_inclusion ψ.specialFibreMap) χs
    (unramifiedNeutralIncidentDynamicParabolic_le_image
      C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub') hrad

end Langlands.BruhatTits.IntegralModels
