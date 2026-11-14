import Langlands.BruhatTits.IntegralModels.UnramifiedTranslatedParabolicAttainment
import Langlands.Geometry.Building.IntegerBuildingFacetClosure

/-! # Quotient parabolics at incident full building facets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

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
    (Q : SpecialFibreQuotientData D)

include hN in
/-- Each supplied quotient parabolic is the actual quotient image of every
supplied generic-identity comparison at one incident full building facet point. -/
theorem exists_incidentBuildingPoint_quotientImage_eq_parabolic
    (hQ : Q.IsReductiveQuotient)
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (i : P ⟶ Q.quotient) (hi : IsParabolicSubgroup i) :
    ∃ z : C.ReducedBuilding,
      C.FacetPrecedes (C.buildingFacetAt (C.apartmentMap x)) (C.buildingFacetAt z) ∧
      ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
        [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
        M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer {z} →
        ∀ φ : M.Hom D.neutral (𝟙 G),
          SubgroupFunctor.range (SchematicImage.inclusion
            (φ.specialFibreMap ≫ Q.projection)) = SubgroupFunctor.range i := by
  obtain ⟨s, hs, ν, ε, hε, hface, heq⟩ :=
    exists_incidentRay_conjugate_quotientImage_eq_parabolic
      C E D x hN Q hQ hpositive P i hi
  let g := D.neutral.integralPointMap s
  let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
  let w := C.cocharacterDirection (A.cocharacterSpecialization.symm ν)
  let y := ε • w +ᵥ x
  let z := g⁻¹ • C.apartmentMap y
  have hgfix : g • C.apartmentMap x = C.apartmentMap x :=
    C.apartment.mem_pointwiseFixer.mp hs.2 _ ⟨x, Set.mem_singleton x, rfl⟩
  have hginvfix : C.translatedApartmentMap g⁻¹ x = C.apartmentMap x := by
    change g⁻¹ • C.apartmentMap x = C.apartmentMap x
    calc
      g⁻¹ • C.apartmentMap x = g⁻¹ • (g • C.apartmentMap x) :=
        congrArg (g⁻¹ • ·) hgfix.symm
      _ = C.apartmentMap x := inv_smul_smul g _
  refine ⟨z, ⟨g⁻¹, AffineRootSystem.facet C.affineRoots x,
    AffineRootSystem.facet C.affineRoots y, hface, ?_, ?_⟩, ?_⟩
  · exact (congrArg (fun p => (C.buildingFacetAt p).val) hginvfix.symm).trans
      (C.buildingFacetAt_translatedApartmentMap g⁻¹ x)
  · exact C.buildingFacetAt_translatedApartmentMap g⁻¹ y
  · intro M hMsmooth hMconnected hM φ
    let L := M.transport (G.innerIso (D.neutral.integralPointMap s⁻¹)⁻¹)
    let : Smooth L.group.X.hom := hMsmooth
    let : GeometricallyConnected L.group.X.hom := hMconnected
    have hL : L.integralPoints = E.zeroPoints ⊓
        C.pointwiseFixer (C.apartmentMap '' {y}) := by
      have ht := integralPoints_transport_eq_translated_zeroFixer C E
        (D.neutral.integralPointMap s⁻¹)⁻¹ {z} M hM
      simpa only [L, z, g, map_inv, inv_inv, Set.smul_set_singleton,
        smul_inv_smul, Set.image_singleton] using ht
    have himage := heq L hL (φ.conjugateSource s⁻¹)
    have hproj : D.neutral.reduction s⁻¹ ≫ Q.projection.hom.hom =
        (D.neutral.reduction s ≫ Q.projection.hom.hom)⁻¹ := by
      rw [map_inv]
      exact map_inv (rationalPoints.map Q.projection) (D.neutral.reduction s)
    rw [φ.conjugateSource_specialFibreMap_comp s⁻¹ Q.projection,
      hproj, ← innerIso_inv_hom, inv_inv, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at himage
    exact himage

/-- Conditional quotient attainment at an actual incident full building facet
point, uniformly over all supplied characterized source models and comparisons. -/
def HasIncidentBuildingQuotientAttainment : Prop :=
  D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) →
    Q.IsReductiveQuotient → UnramifiedRootPositiveReductionStatement.{u} →
    ∀ (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : P ⟶ Q.quotient), IsParabolicSubgroup i →
      ∃ z : C.ReducedBuilding,
        C.FacetPrecedes (C.buildingFacetAt (C.apartmentMap x)) (C.buildingFacetAt z) ∧
        ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
          [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
          M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer {z} →
          ∀ φ : M.Hom D.neutral (𝟙 G),
            SubgroupFunctor.range (SchematicImage.inclusion
              (φ.specialFibreMap ≫ Q.projection)) = SubgroupFunctor.range i

theorem hasIncidentBuildingQuotientAttainment :
    HasIncidentBuildingQuotientAttainment C E D x Q := by
  intro hN hQ hpositive P i hi
  exact exists_incidentBuildingPoint_quotientImage_eq_parabolic C E D x hN Q
    hQ hpositive P i hi

end Langlands.BruhatTits.IntegralModels
