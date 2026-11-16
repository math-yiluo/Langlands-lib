import Langlands.Geometry.Building.UnramifiedBuildingFacetRecovery
import Langlands.Geometry.Building.IntegerBuildingFacetFixers
import Langlands.BruhatTits.IntegralModels.SpecialFibreImageRecovery
import Langlands.BruhatTits.IntegralModels.FacetParabolicTransfer
import Langlands.BruhatTits.IntegralModels.IntegerFacetImageFunctoriality

/-! # Recovering actual integer-building facets from their quotient images -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)

/-- Full-facet zero-fixer containment is exactly reverse facet incidence. -/
theorem buildingZeroFixer_le_iff_facetPrecedes (J J' : C.BuildingFacet) :
    E.zeroPoints ⊓ C.pointwiseFixer J.val ≤
        E.zeroPoints ⊓ C.pointwiseFixer J'.val ↔
      C.FacetPrecedes J' J := by
  constructor
  · exact E.facetPrecedes_of_buildingZeroFixer_le C
      (J.property.nonempty C) (Set.Subset.refl _)
      (J'.property.nonempty C) (Set.Subset.refl _)
  · intro h
    exact inf_le_inf_left E.zeroPoints (C.pointwiseFixer_le_of_facetPrecedes h)

end Langlands.Geometry.Building.UnramifiedZeroDatum

namespace Langlands.BruhatTits.IntegralModels.IntegerFacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)
  {R : Type u} [CommRing R] [IsDomain R]
  [Algebra R (UnramifiedClosure F)] [IsFractionRing R (UnramifiedClosure F)]
  (M : IntegerFacetModelData C R)

/-- A supplied full neutral integral-point characterization identifies integral
point containment with reverse incidence in the actual upstairs building. -/
theorem neutral_integralPoints_le_iff_facetPrecedes
    (hsource : ∀ J : C.BuildingFacet,
      (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val)
    (J J' : C.BuildingFacet) :
    (M.model J).neutral.integralPoints ≤ (M.model J').neutral.integralPoints ↔
      C.FacetPrecedes J' J := by
  rw [hsource J, hsource J']
  exact E.buildingZeroFixer_le_iff_facetPrecedes C J J'

section Local

variable [IsLocalRing R] (Fc : C.BuildingFacet)
  (Q : SpecialFibreQuotientData (M.model Fc))

/-- A parabolic actual neutral special-fibre image gives a parabolic quotient
image, with the exact all-test inverse image in the original special fibre. -/
theorem unramifiedIncidentParabolicImage_isParabolic_and_comap
    (hQ : Q.IsReductiveQuotient) (J : C.IncidentFacets Fc)
    (hpar : (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage) :
    IsParabolicFunctor (M.incidentParabolicImage Fc Q J) ∧
      (M.incidentParabolicImage Fc Q J).comap Q.projection =
        SubgroupFunctor.range
          (M.morphism Fc J.val J.property).specialFibreImageInclusion := by
  let φ := M.morphism Fc J.val J.property
  obtain ⟨hp, heq⟩ := φ.parabolicReductiveImage_and_comap Q hQ hpar
  exact ⟨⟨φ.reductiveImage Q, φ.reductiveImageInclusion Q, hp, rfl⟩, heq⟩

end Local

variable [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  (Fc : C.BuildingFacet) (Q : SpecialFibreQuotientData (M.model Fc))

/-- Containment of the actual quotient images reflects reverse incidence.
The full neutral characterization, congruence and parabolicity inputs remain
explicit; no no-inversions or downstairs building restriction is needed. -/
theorem unramifiedIncidentParabolicImage_le_iff
    (hsource : ∀ J : C.BuildingFacet,
      (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val)
    (hQ : Q.IsReductiveQuotient) (J J' : C.IncidentFacets Fc)
    (hker : (M.model Fc).neutral.congruenceSubgroup ≤
      (M.model J.val).neutral.integralPoints)
    (hker' : (M.model Fc).neutral.congruenceSubgroup ≤
      (M.model J'.val).neutral.integralPoints)
    (hpar : (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage)
    (hpar' : (M.morphism Fc J'.val J'.property).HasParabolicSpecialFibreImage) :
    M.incidentParabolicImage Fc Q J ≤ M.incidentParabolicImage Fc Q J' ↔
      C.FacetPrecedes J'.val J.val := by
  constructor
  · intro hle
    apply (M.neutral_integralPoints_le_iff_facetPrecedes E C hsource J.val J'.val).mp
    apply ((M.morphism Fc J.val J.property).specialFibreImage_le_iff_integralPoints_le
      (M.morphism Fc J'.val J'.property) hker hker').mp
    rw [← (M.unramifiedIncidentParabolicImage_isParabolic_and_comap C Fc Q hQ J hpar).2,
      ← (M.unramifiedIncidentParabolicImage_isParabolic_and_comap C Fc Q hQ J' hpar').2]
    exact SubgroupFunctor.comap_mono hle
  · exact M.incidentParabolicImage_le Fc Q

/-- The actual incident-facet quotient-image map is injective under the
explicit neutral characterization, congruence and parabolicity inputs. -/
theorem unramifiedIncidentParabolicImage_injective
    (hsource : ∀ J : C.BuildingFacet,
      (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val)
    (hQ : Q.IsReductiveQuotient)
    (hker : ∀ J : C.IncidentFacets Fc,
      (M.model Fc).neutral.congruenceSubgroup ≤ (M.model J.val).neutral.integralPoints)
    (hpar : ∀ J : C.IncidentFacets Fc,
      (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage) :
    Function.Injective (M.incidentParabolicImage Fc Q) := by
  intro J J' heq
  apply Subtype.ext
  exact C.facetPrecedes_antisymm
    ((M.unramifiedIncidentParabolicImage_le_iff E C Fc Q hsource hQ
      J' J (hker J') (hker J) (hpar J') (hpar J)).mp heq.ge)
    ((M.unramifiedIncidentParabolicImage_le_iff E C Fc Q hsource hQ
      J J' (hker J) (hker J') (hpar J) (hpar J')).mp heq.le)

/-- Explicit inputs for faithful actual quotient-image order and parabolicity
on the full incident facets of the maximal-unramified integer building. -/
def UnramifiedIntegerFacetImageRecoveryStatement : Prop :=
  (∀ J : C.BuildingFacet,
    (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val) →
  Q.IsReductiveQuotient →
  (∀ J : C.IncidentFacets Fc,
    (M.model Fc).neutral.congruenceSubgroup ≤ (M.model J.val).neutral.integralPoints) →
  (∀ J : C.IncidentFacets Fc,
    (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage) →
  Set.MapsTo (M.incidentParabolicImage Fc Q) Set.univ {P | IsParabolicFunctor P} ∧
    (∀ J J' : C.IncidentFacets Fc,
      M.incidentParabolicImage Fc Q J ≤ M.incidentParabolicImage Fc Q J' ↔
        C.FacetPrecedes J'.val J.val) ∧
    Function.Injective (M.incidentParabolicImage Fc Q)

/-- Full zero-fixer geometry and actual special-fibre recovery prove the
faithfulness of the actual integer-facet quotient-image correspondence. -/
theorem unramifiedIntegerFacetImageRecovery :
    M.UnramifiedIntegerFacetImageRecoveryStatement E C Fc Q := by
  intro hsource hQ hker hpar
  exact ⟨fun J _ =>
      (M.unramifiedIncidentParabolicImage_isParabolic_and_comap C Fc Q hQ J (hpar J)).1,
    fun J J' => M.unramifiedIncidentParabolicImage_le_iff E C Fc Q hsource hQ
      J J' (hker J) (hker J') (hpar J) (hpar J'),
    M.unramifiedIncidentParabolicImage_injective E C Fc Q hsource hQ hker hpar⟩

end Langlands.BruhatTits.IntegralModels.IntegerFacetModelData
