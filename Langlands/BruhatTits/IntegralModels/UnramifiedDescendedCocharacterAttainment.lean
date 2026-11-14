import Langlands.BruhatTits.IntegralModels.UnramifiedFacetImageOrderDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionProof
import Langlands.Geometry.Building.DescendedApartmentLinearPart
import Langlands.Geometry.Building.UnramifiedZeroFacetNoInversionsProof

/-! # Actual facet models along descended cocharacter rays -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ z : B.ReducedBuilding, B.HasCommonApartmentWith z)
  (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)

private instance descendedRay_affine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

include hD hcommon hequiv hap hfac in
/-- The image of a full downstairs facet has the same zero fixer as any
one of its image points. -/
theorem zeroFixer_image_buildingFacetAt_eq_singleton (z : B.ReducedBuilding) :
    E.zeroPoints ⊓ C.pointwiseFixer (e '' (B.buildingFacetAt z).val) =
      E.zeroPoints ⊓ C.pointwiseFixer {e z} := by
  have hsub : e '' (B.buildingFacetAt z).val ⊆ (C.buildingFacetAt (e z)).val := by
    simpa only [B.facetRestrictionEmbedding_buildingFacetAt C
      (rationalExtend F (inertiaFixedField F) G) e a
      hD hcommon hequiv hap hfac] using
      B.image_subset_facetRestrictionEmbedding C
        (rationalExtend F (inertiaFixedField F) G) e a
        hD hcommon hequiv hap hfac (B.buildingFacetAt z)
  rw [E.zeroFixer_eq_of_nonempty_subset_buildingFacet C
    MaximalUnramified.zeroFacetNoInversions
    ((B.buildingFacetAt z).property.nonempty.image e) hsub,
    E.zeroFixer_singleton_eq_buildingFacet C MaximalUnramified.zeroFacetNoInversions]

end Langlands.Geometry.Building.UnramifiedZeroDatum

namespace Langlands.BruhatTits.IntegralModels.FacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ z : B.ReducedBuilding, B.HasCommonApartmentWith z)
  (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)
  (M : FacetModelData B ↥𝒪[F])
  (hmodel : ∀ Fc : BuildingFacet B,
    (M.model Fc).neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))

private instance descendedAttainment_affine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

local instance : Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[F])
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  unramifiedResidue_isSeparable

include hD hcommon hequiv hap hfac hmodel in
/-- The supplied model at an apartment point is actually characterized by
the upstairs singleton, as required by the cocharacter-ray theorem. -/
theorem unramified_apartmentPointCharacterization (x : B.Apartment) :
    ((M.model (B.buildingFacetAt (B.apartmentMap x))).baseChange
      (fixedFieldIntegers F) (inertiaFixedField F)).neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {a x}) := by
  change (M.model (B.buildingFacetAt (B.apartmentMap x))).neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {a x})
  rw [hmodel, E.zeroFixer_image_buildingFacetAt_eq_singleton
    B C e a hD hcommon hequiv hap hfac, hap, Set.image_singleton]

include hD hcommon hequiv hap hfac hmodel in
/-- Every downstairs cocharacter selects an actual incident facet of the
supplied family whose unramified quotient image is its dynamic parabolic. -/
theorem exists_incidentFacet_quotientImage_eq_descendedCocharacter
    (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)
    (hf : f ≫ C.i =
      (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (x : B.Apartment)
    (Q : SpecialFibreQuotientData (M.model (B.buildingFacetAt (B.apartmentMap x))))
    (hQ : Q.IsReductiveQuotient) (c : cocharacterLattice B.S) :
    let D := (M.model (B.buildingFacetAt (B.apartmentMap x))).baseChange
      (fixedFieldIntegers F) (inertiaFixedField F)
    let T := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {a x}
      (M.unramified_apartmentPointCharacterization
        B C E e a hD hcommon hequiv hap hfac hmodel x)
    let cup := cocharacterLattice.baseChange
      (algebraBaseMap F (inertiaFixedField F)) B.S c ≫ descendedTorusHom B C f
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Fd : IncidentFacets B (B.buildingFacetAt (B.apartmentMap x)),
        Fd.val = B.buildingFacetAt (B.apartmentMap
          ((Submodule.Quotient.mk (ε ⊗ₜ[ℤ] c) : TranslationSpace B.i) +ᵥ x)) ∧
        SubgroupFunctor.range
          (((M.morphism _ Fd.val Fd.property).baseChange
            (fixedFieldIntegers F) (inertiaFixedField F)).reductiveImageInclusion
              (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F))) =
          Dynamic.parabolic
            ((CommGroupScheme.groupHom (T.cocharacterSpecialization cup) ≫
              T.specialFibreInclusion) ≫
                (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).projection) := by
  dsimp only
  let Fc := B.buildingFacetAt (B.apartmentMap x)
  let D := (M.model Fc).baseChange (fixedFieldIntegers F) (inertiaFixedField F)
  have hN := M.unramified_apartmentPointCharacterization
    B C E e a hD hcommon hequiv hap hfac hmodel x
  let T := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {a x} hN
  let cup := cocharacterLattice.baseChange
    (algebraBaseMap F (inertiaFixedField F)) B.S c ≫ descendedTorusHom B C f
  let Qup := Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)
  obtain ⟨ε, hε, hface, himage⟩ :=
    exists_pos_incidentFacet_quotientImage_eq_parabolic
      C E D (a x) hN Qup
      (Q.isReductiveQuotient_baseChange _ _ hQ) unramifiedRootPositiveReduction
      (T.cocharacterSpecialization cup)
  simp only [T, AddEquiv.symm_apply_apply] at hface himage
  let y := (Submodule.Quotient.mk (ε ⊗ₜ[ℤ] c) : TranslationSpace B.i) +ᵥ x
  have hay : a y = ε • C.cocharacterDirection cup +ᵥ a x := by
    have h := descendedApartment_map_vadd e a hequiv hap hf (ε ⊗ₜ[ℤ] c) x
    rw [descendedCocharacterMap_tmul] at h
    have hdir : (Submodule.Quotient.mk (ε ⊗ₜ[ℤ] cup) : TranslationSpace C.i) =
        ε • C.cocharacterDirection cup := by
      change (rootAnnihilator C.i).mkQ (ε ⊗ₜ[ℤ] cup) =
        ε • (rootAnnihilator C.i).mkQ ((1 : ℝ) ⊗ₜ[ℤ] cup)
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact h.trans (congrArg (· +ᵥ a x) hdir)
  have hinc : FacetPrecedes B Fc (B.buildingFacetAt (B.apartmentMap y)) := by
    apply (B.facetRestrictionEmbedding_facetPrecedes_iff C
      (rationalExtend F (inertiaFixedField F) G) e a
      hD hcommon hequiv hap hfac _ _).mp
    dsimp only [Fc]
    rw [B.facetRestrictionEmbedding_buildingFacetAt,
      B.facetRestrictionEmbedding_buildingFacetAt, hap, hap, hay]
    refine ⟨1, _, _, hface, ?_, ?_⟩
    · simpa only [IntegerValuationBuildingData.translatedApartmentMap, one_smul] using
        C.buildingFacetAt_translatedApartmentMap 1 (a x)
    · simpa only [IntegerValuationBuildingData.translatedApartmentMap, one_smul] using
        C.buildingFacetAt_translatedApartmentMap 1
          (ε • C.cocharacterDirection cup +ᵥ a x)
  let Fd : IncidentFacets B Fc := ⟨B.buildingFacetAt (B.apartmentMap y), hinc⟩
  let N := (M.model Fd.val).baseChange (fixedFieldIntegers F) (inertiaFixedField F)
  let φ := (M.morphism Fc Fd.val Fd.property).baseChange
    (fixedFieldIntegers F) (inertiaFixedField F)
  let : Smooth N.neutral.group.X.hom := N.neutral_smooth
  let : GeometricallyConnected N.neutral.group.X.hom := N.neutral_geometricallyConnected
  have hsource : N.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        (C.apartmentMap '' {ε • C.cocharacterDirection cup +ᵥ a x}) := by
    have h := M.unramified_apartmentPointCharacterization
      B C E e a hD hcommon hequiv hap hfac hmodel y
    rw [hay] at h
    exact h
  exact ⟨ε, hε, Fd, rfl, himage N.neutral hsource φ.neutral⟩

/-- Actual supplied facet-model attainment for every cocharacter of the
downstairs apartment torus with its generic upstairs factorization. -/
def HasDescendedCocharacterQuotientAttainment : Prop :=
  ∀ (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp),
    f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i →
    ∀ (x : B.Apartment)
      (Q : SpecialFibreQuotientData (M.model (B.buildingFacetAt (B.apartmentMap x)))),
      Q.IsReductiveQuotient → ∀ c : cocharacterLattice B.S,
      let D := (M.model (B.buildingFacetAt (B.apartmentMap x))).baseChange
        (fixedFieldIntegers F) (inertiaFixedField F)
      let T := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {a x}
        (M.unramified_apartmentPointCharacterization
          B C E e a hD hcommon hequiv hap hfac hmodel x)
      let cup := cocharacterLattice.baseChange
        (algebraBaseMap F (inertiaFixedField F)) B.S c ≫ descendedTorusHom B C f
      ∃ ε : ℝ, 0 < ε ∧
        ∃ Fd : IncidentFacets B (B.buildingFacetAt (B.apartmentMap x)),
          Fd.val = B.buildingFacetAt (B.apartmentMap
            ((Submodule.Quotient.mk (ε ⊗ₜ[ℤ] c) : TranslationSpace B.i) +ᵥ x)) ∧
          SubgroupFunctor.range
            (((M.morphism _ Fd.val Fd.property).baseChange
              (fixedFieldIntegers F) (inertiaFixedField F)).reductiveImageInclusion
                (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F))) =
            Dynamic.parabolic
              ((CommGroupScheme.groupHom (T.cocharacterSpecialization cup) ≫
                T.specialFibreInclusion) ≫
                  (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).projection)

theorem hasDescendedCocharacterQuotientAttainment :
    HasDescendedCocharacterQuotientAttainment
      B C E e a hD hcommon hequiv hap hfac M hmodel := by
  intro f hf x Q hQ c
  exact M.exists_incidentFacet_quotientImage_eq_descendedCocharacter
    B C E e a hD hcommon hequiv hap hfac hmodel f hf x Q hQ c

end Langlands.BruhatTits.IntegralModels.FacetModelData
