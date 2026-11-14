import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRoots
import Langlands.Geometry.Building.IncidentFacetRootFiltration
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.HomImage

/-! # Positive root-model images for incident unramified facets -/

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- A nonempty part of one facet has the same actual root fixer as that
whole facet. AS4 is retained for general apartment data. -/
theorem rootFixer_eq_of_nonempty_subset_facet
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Ω F : Set D.Apartment} (hF : AffineRootSystem.IsFacet D.affineRoots F)
    (hΩ : Ω.Nonempty) (hsub : Ω ⊆ F) (a : relativeRoots i) :
    D.rootFixer a Ω = D.rootFixer a F := by
  obtain ⟨x, hx⟩ := hΩ
  apply le_antisymm
  · rw [(D.rootFixer_eq_filtration_of_isFacet hAS4 hF (hsub hx) a.2).1]
    have h := D.rootFixer_anti a (Set.singleton_subset_iff.mpr hx)
    rwa [D.rootFixer_singleton] at h
  · exact D.rootFixer_anti a hsub

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.IntegralModels

private theorem modelHom_comp_eq
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {H J : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K H} {N P : IntegralModel R K J}
    {f : H ⟶ J} (φ : M.Hom N f) (ψ : N.Hom P (𝟙 J))
    (modelMap : M.Hom P f) : φ.hom ≫ ψ.hom = modelMap.hom := by
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono P.genericIso.hom).mp
  rw [Functor.map_comp, Category.assoc, ψ.generic_comm,
    Category.comp_id, φ.generic_comm, modelMap.generic_comm]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hN' : N'.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    [Smooth N.group.X.hom]

local notation "TΩ" => unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN

/-- The target's actual integral root model extends into the source ambient
model whenever the corresponding root fixers are included. -/
def unramifiedZeroFixerRootModelLift (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    ((TΩ).rootModel a a.2.1).Hom N' ((TΩ).rootInclusion a a.2.1) :=
  Classical.choice
    ((IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
      ((TΩ).rootGroup a a.2.1) G ((TΩ).rootInclusion a a.2.1)
      ((TΩ).rootModel a a.2.1) N'
      (IntegralModel.SplitRoot.model_isSmooth N (TΩ).isSplit (TΩ).inclusion
        ((TΩ).integralCharacter a) ((TΩ).integralCharacter_ne_zero a.2.1))
      (fun g hg => by
        have hg' : rationalPoints.map ((TΩ).rootInclusion a a.2.1) g ∈
            C.apartment.rootFixer a Ω := by
          rw [← unramifiedZeroFixerRootModel_integralPoints_eq C E N Ω hN a]
          exact ⟨g, hg, rfl⟩
        rw [hN']
        have hfix : C.apartment.rootFixer a Ω' ≤
            E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') := by
          rw [← rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω' a]
          exact inf_le_right
        exact hfix (hle hg')))

variable (ψ : N'.Hom N (𝟙 G))

/-- Generic rigidity identifies the lifted map's composite with the
original target root inclusion. -/
theorem unramifiedZeroFixerRootModelLift_comp (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    (unramifiedZeroFixerRootModelLift C E N N' Ω Ω' hN hN' a hle).hom ≫ ψ.hom =
      ((TΩ).rootModelMap a a.2.1).hom := by
  exact modelHom_comp_eq
    (unramifiedZeroFixerRootModelLift C E N N' Ω Ω' hN hN' a hle) ψ
    ((TΩ).rootModelMap a a.2.1)

local instance model_specialFibre_affine
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) :
    IsAffineHom M.specialFibre.X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd M.group.X.hom
      (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  exact MorphismProperty.pullback_snd _ _ M.affine

local instance model_specialFibre_isAffine
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) :
    IsAffine M.specialFibre.X.left :=
  isAffine_of_isAffineHom M.specialFibre.X.hom

/-- The whole special fibre of the actual target root model factors through
the actual schematic image, with no bounded-set hypothesis. -/
def unramifiedZeroFixerRootImageFactor (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    ((TΩ).rootModel a a.2.1).specialFibre ⟶ SchematicImage.image ψ.specialFibreMap :=
  (unramifiedZeroFixerRootModelLift C E N N' Ω Ω' hN hN' a hle).specialFibreMap ≫
    SchematicImage.projection ψ.specialFibreMap

@[reassoc]
theorem unramifiedZeroFixerRootImageFactor_comp (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    unramifiedZeroFixerRootImageFactor C E N N' Ω Ω' hN hN' ψ a hle ≫
        SchematicImage.inclusion ψ.specialFibreMap =
      ((TΩ).rootModelMap a a.2.1).specialFibreMap := by
  unfold unramifiedZeroFixerRootImageFactor
  rw [Category.assoc, SchematicImage.projection_inclusion]
  change
    (GroupScheme.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
        (unramifiedZeroFixerRootModelLift C E N N' Ω Ω' hN hN' a hle).hom ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
        ψ.hom = _
  rw [← Functor.map_comp, unramifiedZeroFixerRootModelLift_comp]
  rfl

include hN' in
/-- This is containment of subgroup functors on every residue-scheme test. -/
theorem unramifiedZeroFixerRoot_range_le_image (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    SubgroupFunctor.range ((TΩ).rootModelMap a a.2.1).specialFibreMap ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) := by
  rw [← unramifiedZeroFixerRootImageFactor_comp C E N N' Ω Ω' hN hN' ψ a hle]
  intro T z hz
  rw [SubgroupFunctor.mem_range] at hz ⊢
  rcases hz with ⟨w, rfl⟩
  exact ⟨w ≫ (unramifiedZeroFixerRootImageFactor C E N N' Ω Ω' hN hN' ψ a hle).hom.hom,
    by rw [Grp.comp_hom_hom, Category.assoc]⟩

section Incident

variable {Fa Ca : Set C.Apartment}
  (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
  (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
  (hΩ : Ω.Nonempty) (hΩ' : Ω'.Nonempty)
  (hsub : Ω ⊆ Fa) (hsub' : Ω' ⊆ Ca)

include hΩ hΩ' hsub hsub' in
/-- Nonempty portions of the two incident facets have equal root fixers
for every root positive on the same chosen adapted cocharacter. -/
theorem rootFixer_eq_of_incidentFacetCocharacter_pos_of_subsets
    (a : relativeRoots C.i)
    (ha : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa)) :
    C.apartment.rootFixer a Ω = C.apartment.rootFixer a Ω' := by
  rw [C.apartment.rootFixer_eq_of_nonempty_subset_facet
    C.affineRoot_mem_or_two_smul_mem hFaCa.1 hΩ hsub a,
    C.apartment.rootFixer_eq_of_nonempty_subset_facet
      C.affineRoot_mem_or_two_smul_mem hCa hΩ' hsub' a]
  exact C.rootFixer_eq_of_incidentFacetCocharacter_pos hCa hFaCa a ha

/-- A positive-root factor for actual zero-fixer models of nonempty portions
of incident facets, without supplied root-model or extension data. -/
def unramifiedIncidentPositiveRootImageFactor (a : relativeRoots C.i)
    (ha : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa)) :
    ((TΩ).rootModel a a.2.1).specialFibre ⟶ SchematicImage.image ψ.specialFibreMap :=
  unramifiedZeroFixerRootImageFactor C E N N' Ω Ω' hN hN' ψ a
    (rootFixer_eq_of_incidentFacetCocharacter_pos_of_subsets
      C Ω Ω' hCa hFaCa hΩ hΩ' hsub hsub' a ha).le

@[reassoc]
theorem unramifiedIncidentPositiveRootImageFactor_comp (a : relativeRoots C.i)
    (ha : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa)) :
    unramifiedIncidentPositiveRootImageFactor
        C E N N' Ω Ω' hN hN' ψ hCa hFaCa hΩ hΩ' hsub hsub' a ha ≫
        SchematicImage.inclusion ψ.specialFibreMap =
      ((TΩ).rootModelMap a a.2.1).specialFibreMap :=
  unramifiedZeroFixerRootImageFactor_comp C E N N' Ω Ω' hN hN' ψ a _

include hN' hΩ hΩ' hsub hsub' in
theorem unramifiedIncidentPositiveRoot_range_le_image (a : relativeRoots C.i)
    (ha : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa)) :
    SubgroupFunctor.range ((TΩ).rootModelMap a a.2.1).specialFibreMap ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) :=
  unramifiedZeroFixerRoot_range_le_image C E N N' Ω Ω' hN hN' ψ a
    (rootFixer_eq_of_incidentFacetCocharacter_pos_of_subsets
      C Ω Ω' hCa hFaCa hΩ hΩ' hsub hsub' a ha).le

end Incident

end Langlands.BruhatTits.IntegralModels
