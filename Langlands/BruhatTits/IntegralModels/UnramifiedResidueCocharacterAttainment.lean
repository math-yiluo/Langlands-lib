import Langlands.BruhatTits.IntegralModels.UnramifiedDescendedCocharacterAttainment
import Langlands.BruhatTits.IntegralModels.IntegralCocharacterComparison
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Actual facet models for downstairs residue cocharacter parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

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
/-- Every cocharacter of a supplied downstairs split integral torus gives
an actual incident facet whose quotient image is its residue parabolic. -/
theorem exists_incidentFacet_quotientImage_eq_residueCocharacter
    (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)
    (hf : f ≫ C.i =
      (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (x : B.Apartment)
    (Q : SpecialFibreQuotientData (M.model (B.buildingFacetAt (B.apartmentMap x))))
    (hQ : Q.IsReductiveQuotient)
    (T : IntegralTorusData (M.model (B.buildingFacetAt (B.apartmentMap x))) B.S B.i)
    (hT : IsSplitTorus T.torus.toGrp) (c : cocharacterLattice B.S) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Fd : IncidentFacets B (B.buildingFacetAt (B.apartmentMap x)),
        Fd.val = B.buildingFacetAt (B.apartmentMap
          ((Submodule.Quotient.mk (ε ⊗ₜ[ℤ] c) : TranslationSpace B.i) +ᵥ x)) ∧
        SubgroupFunctor.range
          ((M.morphism _ Fd.val Fd.property).reductiveImageInclusion Q) =
          Dynamic.parabolic
            ((CommGroupScheme.groupHom (T.cocharacterSpecialization hT c) ≫
              T.specialFibreInclusion) ≫ Q.projection) := by
  let D := (M.model (B.buildingFacetAt (B.apartmentMap x))).baseChange
    (fixedFieldIntegers F) (inertiaFixedField F)
  let Tup := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {a x}
    (M.unramified_apartmentPointCharacterization
      B C E e a hD hcommon hequiv hap hfac hmodel x)
  obtain ⟨ε, hε, Fd, hFd, himage⟩ :=
    M.exists_incidentFacet_quotientImage_eq_descendedCocharacter
      B C E e a hD hcommon hequiv hap hfac hmodel f hf x Q hQ c
  refine ⟨ε, hε, Fd, hFd, ?_⟩
  let φ := M.morphism _ Fd.val Fd.property
  have hpar := T.baseChange_quotientParabolic
    (fixedFieldIntegers F) (inertiaFixedField F) hT Tup f hf Q c
  change SubgroupFunctor.range
      ((φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).reductiveImageInclusion
        (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F))) = _ at himage
  rw [hpar, ← φ.reductiveImage_range_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) Q] at himage
  let b := algebraBaseMap (IsLocalRing.ResidueField ↥𝒪[F])
    (IsLocalRing.ResidueField (fixedFieldIntegers F))
  have hb := fieldExtension_fpqc (IsLocalRing.ResidueField ↥𝒪[F])
    (IsLocalRing.ResidueField (fixedFieldIntegers F))
  let : Surjective b := hb.1
  let : Flat b := hb.2.1
  let : QuasiCompact b := hb.2.2
  let : IsAffine Q.quotient.X.left := isAffine_of_isAffineHom Q.quotient.X.hom
  have hrep : (SubgroupFunctor.range (φ.reductiveImageInclusion Q)).IsRepresentedBy
      (φ.reductiveImageInclusion Q) :=
    ⟨inferInstanceAs (Mono (SchematicImage.inclusionOver _)), rfl⟩
  exact SubgroupFunctor.eq_of_isRepresentedBy_baseChange_eq b hrep
    (Dynamic.Affine.isRepresentedBy_parabolicHom _) himage

/-- Actual supplied facet-model attainment over the downstairs residue field
for cocharacters of a supplied split integral apartment torus. -/
def HasResidueCocharacterQuotientAttainment : Prop :=
  ∀ (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp),
    f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i →
    ∀ (x : B.Apartment)
      (Q : SpecialFibreQuotientData (M.model (B.buildingFacetAt (B.apartmentMap x)))),
      Q.IsReductiveQuotient →
      ∀ (T : IntegralTorusData
          (M.model (B.buildingFacetAt (B.apartmentMap x))) B.S B.i),
        ∀ (hT : IsSplitTorus T.torus.toGrp) (c : cocharacterLattice B.S),
        ∃ ε : ℝ, 0 < ε ∧
          ∃ Fd : IncidentFacets B (B.buildingFacetAt (B.apartmentMap x)),
            Fd.val = B.buildingFacetAt (B.apartmentMap
              ((Submodule.Quotient.mk (ε ⊗ₜ[ℤ] c) : TranslationSpace B.i) +ᵥ x)) ∧
            SubgroupFunctor.range
              ((M.morphism _ Fd.val Fd.property).reductiveImageInclusion Q) =
              Dynamic.parabolic
                ((CommGroupScheme.groupHom (T.cocharacterSpecialization hT c) ≫
                  T.specialFibreInclusion) ≫ Q.projection)

include hD hcommon hequiv hap hfac hmodel in
theorem hasResidueCocharacterQuotientAttainment :
    HasResidueCocharacterQuotientAttainment B C M := by
  intro f hf x Q hQ T hT c
  exact M.exists_incidentFacet_quotientImage_eq_residueCocharacter
    B C E e a hD hcommon hequiv hap hfac hmodel f hf x Q hQ T hT c

end Langlands.BruhatTits.IntegralModels.FacetModelData
