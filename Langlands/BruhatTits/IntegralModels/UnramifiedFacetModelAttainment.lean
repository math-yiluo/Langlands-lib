import Langlands.BruhatTits.IntegralModels.UnramifiedBuildingParabolicAttainment
import Langlands.Geometry.Building.UnramifiedZeroFacetNoInversionsStatement
import Langlands.Geometry.Building.IntegerBuildingFacetFixers
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # Actual quotient attainment by supplied full-facet models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F G) (C : MaximalUnramified.BuildingData F G)

/-- Under no inversions, any nonempty subset of a full building facet has
the same zero fixer as that whole facet. -/
theorem zeroFixer_eq_of_nonempty_subset_buildingFacet
    (hno : MaximalUnramified.ZeroFacetNoInversionsStatement.{u})
    {Fc : C.BuildingFacet} {Ω : Set C.ReducedBuilding}
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fc.val) :
    E.zeroPoints ⊓ C.pointwiseFixer Ω =
      E.zeroPoints ⊓ C.pointwiseFixer Fc.val := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx⟩ := hne
    have hgx : g • x = x := C.apartment.mem_pointwiseFixer.mp hg.2 x hx
    have htranslate : (g • ·) '' Fc.val = Fc.val :=
      (Fc.property.smul C g).eq_of_mem_mem C Fc.property
        ⟨x, hΩ hx, hgx⟩ (hΩ hx)
    exact ⟨hg.1, hno.mem_pointwiseFixer_of_isFacet C E Fc.property hg.1
      htranslate.le⟩
  · intro g hg
    exact ⟨hg.1, C.apartment.mem_pointwiseFixer.mpr
      (fun y hy => C.apartment.mem_pointwiseFixer.mp hg.2 y (hΩ hy))⟩

/-- Under no inversions, a point and its full building facet have identical
zero fixers in the original rational-point group. -/
theorem zeroFixer_singleton_eq_buildingFacet
    (hno : MaximalUnramified.ZeroFacetNoInversionsStatement.{u})
    (z : C.ReducedBuilding) :
    E.zeroPoints ⊓ C.pointwiseFixer {z} =
      E.zeroPoints ⊓ C.pointwiseFixer (C.buildingFacetAt z).val :=
  E.zeroFixer_eq_of_nonempty_subset_buildingFacet C hno
    (Set.singleton_nonempty z)
    (Set.singleton_subset_iff.mpr (C.mem_buildingFacetAt z))

end Langlands.Geometry.Building.UnramifiedZeroDatum

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (x : C.Apartment)
    (hN : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))

include hN in
/-- Incidence and the proved strictly Henselian extension theorem construct
a generic-identity comparison from every supplied smooth full-facet model. -/
theorem nonempty_hom_of_incidentBuildingFacet
    {Fc : C.BuildingFacet}
    (hFc : C.FacetPrecedes (C.buildingFacetAt (C.apartmentMap x)) Fc)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth M.group.X.hom]
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer Fc.val) :
    Nonempty (M.Hom D.neutral (𝟙 G)) := by
  apply IntegralModel.fixedField_hasSmoothHomExtension
    IntegralModel.smoothHomExtension F G G (𝟙 G) M D.neutral
    (inferInstanceAs (Smooth M.group.X.hom))
  intro g hg
  have hg' : g ∈ E.zeroPoints ⊓ C.pointwiseFixer Fc.val := hM ▸ hg
  have hbase := C.pointwiseFixer_le_of_facetPrecedes hFc hg'.2
  have hpoint : g • C.apartmentMap x = C.apartmentMap x :=
    C.apartment.mem_pointwiseFixer.mp hbase _ (C.mem_buildingFacetAt _)
  have htarget : g ∈ D.neutral.integralPoints := by
    rw [hN, Set.image_singleton]
    exact ⟨hg'.1, C.apartment.mem_pointwiseFixer.mpr (by
      simpa only [Set.forall_mem_singleton] using hpoint)⟩
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using htarget

include hN in
/-- Each actual quotient parabolic is attained at a full incident facet.
Every supplied smooth connected model there admits a comparison, and every
such comparison has the prescribed actual quotient image. -/
theorem exists_incidentFacet_model_quotientImage_eq_parabolic
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (hno : MaximalUnramified.ZeroFacetNoInversionsStatement.{u})
    (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (i : P ⟶ Q.quotient) (hi : IsParabolicSubgroup i) :
    ∃ Fc : C.BuildingFacet,
      C.FacetPrecedes (C.buildingFacetAt (C.apartmentMap x)) Fc ∧
      ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
        [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
        M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer Fc.val →
        Nonempty (M.Hom D.neutral (𝟙 G)) ∧
          ∀ φ : M.Hom D.neutral (𝟙 G),
            SubgroupFunctor.range (SchematicImage.inclusion
              (φ.specialFibreMap ≫ Q.projection)) = SubgroupFunctor.range i := by
  obtain ⟨z, hz, himage⟩ :=
    exists_incidentBuildingPoint_quotientImage_eq_parabolic C E D x hN Q
      hQ hpositive P i hi
  refine ⟨C.buildingFacetAt z, hz, ?_⟩
  intro M _ _ hM
  refine ⟨nonempty_hom_of_incidentBuildingFacet C E D x hN hz M hM, ?_⟩
  apply himage M
  rw [E.zeroFixer_singleton_eq_buildingFacet C hno z]
  exact hM

/-- Conditional attainment by supplied full-facet models, including actual
comparison existence and equality on every scheme test. -/
def HasIncidentFacetModelQuotientAttainment (Q : SpecialFibreQuotientData D) : Prop :=
  D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) →
    Q.IsReductiveQuotient → UnramifiedRootPositiveReductionStatement.{u} →
    MaximalUnramified.ZeroFacetNoInversionsStatement.{u} →
    ∀ (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : P ⟶ Q.quotient), IsParabolicSubgroup i →
      ∃ Fc : C.BuildingFacet,
        C.FacetPrecedes (C.buildingFacetAt (C.apartmentMap x)) Fc ∧
        ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
          [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
          M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer Fc.val →
          Nonempty (M.Hom D.neutral (𝟙 G)) ∧
            ∀ φ : M.Hom D.neutral (𝟙 G),
              SubgroupFunctor.range (SchematicImage.inclusion
                (φ.specialFibreMap ≫ Q.projection)) = SubgroupFunctor.range i

theorem hasIncidentFacetModelQuotientAttainment (Q : SpecialFibreQuotientData D) :
    HasIncidentFacetModelQuotientAttainment C E D x Q := by
  intro hN hQ hpositive hno P i hi
  exact exists_incidentFacet_model_quotientImage_eq_parabolic C E D x hN Q
    hQ hpositive hno P i hi

end Langlands.BruhatTits.IntegralModels
