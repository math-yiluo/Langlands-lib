import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentGenericity
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentDynamicImage
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCentralizerImage
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRadicalImage
import Langlands.GroupScheme.Absolute.RadicalDynamicParabolicRecognition
import Langlands.GroupScheme.HomImage

/-! # Conditional parabolicity of actual incident special-fibre images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

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
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] [ConnectedSpace N.specialFibre.X.left]
    (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hN' : N'.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (ψ : N'.Hom N (𝟙 G))
    {Fa Ca : Set C.Apartment}
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
    (hΩ : Ω.Nonempty) (hΩ' : Ω'.Nonempty)
    (hsub : Ω ⊆ Fa) (hsub' : Ω' ⊆ Ca)

local notation "A" => unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN
local notation "νS" =>
  IntegralSplitTorusData.cocharacterSpecialization
    (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN)
    (C.incidentFacetCocharacter hCa hFaCa)
local notation "χS" => CommGroupScheme.groupHom νS ≫
  IntegralSplitTorusData.specialFibreInclusion
    (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN)

private instance incidentParabolic_specialFibre_affine
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom M.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom M.group.X.hom))

private instance incidentParabolic_specialFibre_smooth
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth M.group.X.hom] : Smooth M.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth M.group.X.hom))

include hN' hΩ hΩ' hsub hsub' in
/-- The actual dynamic parabolic of the specialized incident cocharacter lies
in the actual comparison image on every residue-scheme test. -/
theorem unramifiedIncidentDynamicParabolic_le_image :
    Dynamic.parabolic χS ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) := by
  apply parabolic_le_of_torusCentralizer_le_of_unipotent_le
    (A).specialFibreTorus_isSplit (A).specialFibreInclusion νS
    (unramifiedIncidentCocharacter_specialization_isGeneric C E N Ω hN hCa hFaCa)
  · exact unramifiedZeroFixer_specialCentralizer_le_image
      C E N N' Ω Ω' hN hN' hΩ ψ
  · exact unramifiedIncidentDynamicUnipotent_le_image
      C E N N' Ω Ω' hN hN' ψ hCa hFaCa hΩ hΩ' hsub hsub'

/-- The canonical inclusion of incident dynamic parabolic points into the
actual comparison-image points, preserving the ambient point. -/
def unramifiedIncidentDynamicParabolicImagePoints
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))) :
    (Dynamic.parabolic χS).carrier T →*
      (SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap)).carrier T :=
  Subgroup.inclusion ((unramifiedIncidentDynamicParabolic_le_image
    C E N N' Ω Ω' hN hN' ψ hCa hFaCa hΩ hΩ' hsub hsub') T)

@[simp]
theorem unramifiedIncidentDynamicParabolicImagePoints_val
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (x : (Dynamic.parabolic χS).carrier T) :
    (unramifiedIncidentDynamicParabolicImagePoints
      C E N N' Ω Ω' hN hN' ψ hCa hFaCa hΩ hΩ' hsub hsub' T x).val = x.val :=
  rfl

variable [Smooth N'.group.X.hom]
    {U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (r : U ⟶ N.specialFibre) (hr : IsUnipotentRadical r)

local instance incidentParabolic_residue_algClosed :
    IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

include hN hN' hCa hFaCa hΩ hΩ' hsub hsub' hr in
/-- For smooth source and connected target fibre, full radical containment
is the remaining input for geometric parabolicity of the actual image. -/
theorem unramifiedIncidentImage_isParabolic_of_radical_le
    (hrad : SubgroupFunctor.range r ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap)) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) := by
  let : GeometricallyReduced N'.specialFibre.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  let : Smooth (SchematicImage.image ψ.specialFibreMap).X.hom :=
    HomImage.smooth_image ψ.specialFibreMap
  exact isParabolicSubgroup_of_dynamic_le_of_radical_le
    r hr (SchematicImage.inclusion ψ.specialFibreMap)
    (HomImage.isClosedSubgroup_inclusion ψ.specialFibreMap) χS
    (unramifiedIncidentDynamicParabolic_le_image
      C E N N' Ω Ω' hN hN' ψ hCa hFaCa hΩ hΩ' hsub hsub') hrad

include hN hN' hCa hFaCa hΩ hΩ' hsub hsub' hr in
/-- The entire upstairs radical-preimage generation bound supplies the
remaining containment and hence parabolicity of the incident image. -/
theorem unramifiedIncidentImage_isParabolic_of_rootGeneration
    (H : Subgroup (rationalPoints G))
    (hH : H ≤ E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap))
    (hgen : ((rationalPoints.map r).range.comap N.reduction).map N.integralPointMap ≤
      H ⊔ ⨆ a : relativeRoots C.i, C.apartment.rootFixerPlus a Ω) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) := by
  apply unramifiedIncidentImage_isParabolic_of_radical_le
    C E N N' Ω Ω' hN hN' ψ hCa hFaCa hΩ hΩ' hsub hsub' r hr
  exact unramifiedIncidentRadical_range_le_image
    C E Ω Ω' hCa hFaCa hΩ hsub hsub' H hH N N' hN' r hgen ψ (inferInstanceAs (Smooth N.group.X.hom)) hr

end Langlands.BruhatTits.IntegralModels
