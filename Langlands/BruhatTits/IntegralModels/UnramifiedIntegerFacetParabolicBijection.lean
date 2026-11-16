import Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetImageRecovery
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetModelAttainment
import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionProof
import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.Geometry.Building.UnramifiedZeroFacetNoInversionsProof

/-! # The actual integer-facet parabolic bijection from explicit model inputs -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {K : Type u} [Field K]
  {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (C : IntegerValuationBuildingData v H)

/-- The original rational-point action transports full integer-building facets. -/
def facetTranslateEquiv (g : rationalPoints H) : C.BuildingFacet ≃ C.BuildingFacet where
  toFun J := ⟨g • J.val, J.property.smul C g⟩
  invFun J := ⟨g⁻¹ • J.val, J.property.smul C g⁻¹⟩
  left_inv J := Subtype.ext (inv_smul_smul g J.val)
  right_inv J := Subtype.ext (smul_inv_smul g J.val)

@[simp] theorem facetTranslateEquiv_val (g : rationalPoints H) (J : C.BuildingFacet) :
    (C.facetTranslateEquiv g J).val = g • J.val := rfl

@[simp] theorem facetTranslateEquiv_inv_apply (g : rationalPoints H) (J : C.BuildingFacet) :
    C.facetTranslateEquiv g⁻¹ (C.facetTranslateEquiv g J) = J :=
  (C.facetTranslateEquiv g).left_inv J

/-- Translating the common apartment chart preserves original full-facet incidence. -/
theorem facetPrecedes_translate (g : rationalPoints H)
    {J J' : C.BuildingFacet} (h : C.FacetPrecedes J J') :
    C.FacetPrecedes (C.facetTranslateEquiv g J) (C.facetTranslateEquiv g J') := by
  obtain ⟨t, Fa, Ca, hFa, hJ, hJ'⟩ := h
  refine ⟨g * t, Fa, Ca, hFa, ?_, ?_⟩
  · change (fun z => g • z) '' J.val = C.translatedApartmentMap (g * t) '' Fa
    rw [hJ, Set.image_image]
    apply Set.image_congr
    intro a _
    exact (mul_smul g t (C.apartmentMap a)).symm
  · change (fun z => g • z) '' J'.val = C.translatedApartmentMap (g * t) '' Ca
    rw [hJ', Set.image_image]
    apply Set.image_congr
    intro a _
    exact (mul_smul g t (C.apartmentMap a)).symm

/-- The containing full facet is equivariant for the original quotient action. -/
theorem buildingFacetAt_eq_translate (g : rationalPoints H) (z : C.ReducedBuilding) :
    C.buildingFacetAt (g • z) = C.facetTranslateEquiv g (C.buildingFacetAt z) :=
  (C.buildingFacetAt_eq_iff_mem _ _).mpr
    (Set.smul_mem_smul_set (C.mem_buildingFacetAt z))

end Langlands.Geometry.Building.IntegerValuationBuildingData

namespace Langlands.BruhatTits.IntegralModels.IntegerFacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)
  (M : IntegerFacetModelData C (fixedFieldIntegers F))
  (hsource : ∀ J : C.BuildingFacet,
    (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val)
  (Fc : C.BuildingFacet) (Q : SpecialFibreQuotientData (M.model Fc))

include hsource in
/-- Every parabolic of the actual quotient at an arbitrary full facet is the
actual quotient image of a supplied incident full-facet model. -/
theorem exists_incidentIntegerFacet_quotientImage_eq_parabolic
    (hQ : Q.IsReductiveQuotient)
    (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (i : P ⟶ Q.quotient) (hi : IsParabolicSubgroup i) :
    ∃ J : C.IncidentFacets Fc,
      M.incidentParabolicImage Fc Q J = SubgroupFunctor.range i := by
  obtain ⟨g, _, ⟨x, rfl⟩, hFc⟩ := Fc.property
  have hpoint : C.buildingFacetAt (C.translatedApartmentMap g x) = Fc := by
    apply (C.buildingFacetAt_eq_iff_mem _ _).mpr
    rw [hFc]
    exact ⟨x, AffineRootSystem.mem_facet_self _ _, rfl⟩
  have hbase : C.facetTranslateEquiv g (C.buildingFacetAt (C.apartmentMap x)) = Fc :=
    (C.buildingFacetAt_eq_translate g (C.apartmentMap x)).symm.trans hpoint
  have hN0 : (M.model Fc).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer {g • C.apartmentMap x} := by
    rw [hsource Fc, ← hpoint]
    exact (E.zeroFixer_singleton_eq_buildingFacet C
      MaximalUnramified.zeroFacetNoInversions _).symm
  let f := H.innerIso g⁻¹
  let D := (M.model Fc).transport f
  let Q' := Q.transport f
  have hN : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) := by
    have ht := integralPoints_transport_eq_translated_zeroFixer C E
      g⁻¹ {g • C.apartmentMap x} (M.model Fc).neutral hN0
    simpa only [D, f, RelativeComponentModelData.transport_neutral,
      Set.smul_set_singleton, inv_smul_smul, Set.image_singleton] using ht
  have hQ' : Q'.IsReductiveQuotient := (Q.isReductiveQuotient_transport_iff f).mpr hQ
  obtain ⟨J0, hJ0, hmodels⟩ := exists_incidentFacet_model_quotientImage_eq_parabolic
    C E D x hN Q' hQ' unramifiedRootPositiveReduction
      MaximalUnramified.zeroFacetNoInversions P i hi
  let J := C.facetTranslateEquiv g J0
  have hJ : C.FacetPrecedes Fc J := by
    have ht := C.facetPrecedes_translate g hJ0
    rwa [hbase] at ht
  let N := (M.model J).neutral.transport f
  let : Smooth N.group.X.hom := (M.model J).neutral_smooth
  let : GeometricallyConnected N.group.X.hom := (M.model J).neutral_geometricallyConnected
  have hNJ : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J0.val := by
    have ht := integralPoints_transport_eq_translated_zeroFixer C E
      g⁻¹ J.val (M.model J).neutral (hsource J)
    simpa only [N, f, J, IntegerValuationBuildingData.facetTranslateEquiv_val,
      inv_smul_smul] using ht
  let φ := (M.morphism Fc J hJ).transport f
  exact ⟨⟨J, hJ⟩, (hmodels N hNJ).2 φ.neutral⟩

include hsource in
/-- The actual integer-facet quotient-image map attains every parabolic
subgroup functor, including at full facets outside the chosen apartment. -/
theorem unramifiedIncidentParabolicImage_surjOn (hQ : Q.IsReductiveQuotient) :
    Set.SurjOn (M.incidentParabolicImage Fc Q) Set.univ {P | IsParabolicFunctor P} := by
  intro P hP
  obtain ⟨I, i, hi, hI⟩ := hP
  obtain ⟨J, hJ⟩ := M.exists_incidentIntegerFacet_quotientImage_eq_parabolic
    E C hsource Fc Q hQ I i hi
  exact ⟨J, Set.mem_univ J, hJ.trans hI⟩

local instance : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
local instance : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

include hsource in
/-- Actual parabolicity and congruence containment complete the original
integer-facet parabolic bijection; attainment and injectivity are proved. -/
theorem hasUnramifiedIntegerFacetParabolicOrderBijection
    (hQ : Q.IsReductiveQuotient)
    (hker : ∀ J : C.IncidentFacets Fc,
      (M.model Fc).neutral.congruenceSubgroup ≤ (M.model J.val).neutral.integralPoints)
    (hpar : ∀ J : C.IncidentFacets Fc,
      (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage) :
    M.HasFacetParabolicOrderBijection Fc Q := by
  have hr := M.unramifiedIntegerFacetImageRecovery E C Fc Q hsource hQ hker hpar
  apply (M.hasFacetParabolicOrderBijection_iff_bijOn Fc Q).mpr
  exact ⟨hr.1, fun _ _ _ _ heq => hr.2.2 heq,
    M.unramifiedIncidentParabolicImage_surjOn E C hsource Fc Q hQ⟩

/-- The remaining genuine model inputs for the actual full integer-facet
parabolic bijection, with arbitrary target facet and actual quotient data. -/
def UnramifiedIntegerFacetParabolicBijectionStatement : Prop :=
  (∀ J : C.BuildingFacet,
    (M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val) →
  Q.IsReductiveQuotient →
  (∀ J : C.IncidentFacets Fc,
    (M.model Fc).neutral.congruenceSubgroup ≤ (M.model J.val).neutral.integralPoints) →
  (∀ J : C.IncidentFacets Fc,
    (M.morphism Fc J.val J.property).HasParabolicSpecialFibreImage) →
  M.HasFacetParabolicOrderBijection Fc Q

theorem unramifiedIntegerFacetParabolicBijection :
    M.UnramifiedIntegerFacetParabolicBijectionStatement E C Fc Q := by
  intro hs hQ hker hpar
  exact M.hasUnramifiedIntegerFacetParabolicOrderBijection E C hs Fc Q hQ hker hpar

end Langlands.BruhatTits.IntegralModels.IntegerFacetModelData
