import Langlands.Geometry.Building.UnramifiedDescentOfGroupAxioms.SpecialTorusComparison
import Langlands.Geometry.Building.IntegralModelAxiomsProof

/-! # Unramified descent of group-valid Bruhat–Tits data -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

open UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "𝕂" => inertiaFixedField F
local notation "G_K" => baseChanged F 𝕂 G
local notation "b" => algebraBaseMap F 𝕂

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

set_option maxHeartbeats 10000000 in
private theorem exists_descended_datum (D : KPBuildingDatum G) (hD : D.SatisfiesGroupAxioms) :
    ∃ D' : KPBuildingDatum G,
      D'.SatisfiesGroupAxioms ∧ D'.SatisfiesUnramifiedDescent ∧
        Nonempty (KPBuildingDatum.BuildingEquivalence D D') := by
  let B := D.base.toValuationBuildingData
  have hG := D.base.isConnectedReductive
  obtain ⟨T, i, f, hf, hc, hi⟩ := specialTorusExistence F G hG B.S B.i B.isMaximalSplitTorus
  have : Mono ((GroupScheme.baseChange b).map i).hom.hom.left := mono_of_isMaximalSplitTorus hi
  have hT : IsTorus T.toGrp := IsTorus.of_baseChange (K := 𝕂) hi.isSplitSubtorus.1.isTorus
  have hGK : IsConnectedReductive G_K := connectedReductiveFieldExtensionStatement F 𝕂 G hG
  obtain ⟨A, Z, h6⟩ := exists_omegaCompatible
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)
    quasiSplitIntegerApartmentExistence i hGK hi
  have hA : KPApartmentData.GaloisStable F 𝕂 i A :=
    MaximalUnramified.galoisStable_of_isOmegaCompatible i hc hGK hi A Z h6
  let C := buildingData i hGK hi A Z h6
  let Γ := semilinearData i hGK hi Z h6 hA
  obtain ⟨H⟩ := referenceApartmentDescent B ⟨D.realization, hD.building⟩ i f hf hGK hi A Z h6 hA
  have hfacets (w : B.Apartment) :
      H.apartment ⁻¹' AffineRootSystem.facet C.affineRoots (H.apartment w) =
        AffineRootSystem.facet B.affineRoots w :=
    (AffineRootSystem.facet_restrictedRoots_eq_preimage H.apartment C.affineRoots w).symm.trans
      (congrArg (fun roots => AffineRootSystem.facet roots w) H.roots)
  have hkernel (s) (hs) (w : B.Apartment) := H.torus_units w s hs
  obtain ⟨M, hM, hfull, hneutral⟩ := BuildingModelFamily.exists_satisfiesModelAxioms_withBaseChange_of_unramified
    D.base D.realization D.splitting hD.building hD.boundedSubgroups hD.affineStructure
    hD.affineRootSystem.rootReflections hD.affineRootSystem.apartmentAxioms
    hD.affineRootSystem.compatibleApartmentFacets hD.titsSystem unramifiedParahoricModel
    unramifiedSmoothModelDescent unramifiedZeroDescent unramifiedSmoothHomExtension
    unramifiedOneFixerClosure unramifiedZeroFixerAffineRoot unramifiedTorusClause C Γ
    H.embedding H.apartment H.injective H.equivariant H.apartment_compatible H.fixed hfacets hkernel
  have hParabolicImage := unramifiedFacetParabolicImage_of_generation_positive_modelKernel
    unramifiedUpstairsRadicalRootGeneration unramifiedFacetPositiveRadical unramifiedModelKernel
  let E := unramifiedZeroDatumOfParahoric D.base
  obtain ⟨Q, ρ, hQ⟩ := BuildingModelFamily.exists_satisfiesMorphismAxioms_of_unramified
    D.base D.realization D.splitting hD.building hD.boundedSubgroups hD.affineStructure
    hD.affineRootSystem.rootReflections hD.affineRootSystem.apartmentAxioms
    hD.affineRootSystem.compatibleApartmentFacets hD.titsSystem unramifiedModelKernel
    hParabolicImage unramifiedFacetParabolicOrder unramifiedFacetCommonTorus
    unramifiedFacetRootDatum unramifiedFacetPositiveRadical M C Γ H.embedding H.apartment
    H.injective H.equivariant H.apartment_compatible H.fixed H.surjective_fixed H.special
    hfacets hkernel E hneutral hM.torus_clause
  let D' : KPBuildingDatum G := { D with models := M, quotients := Q, rootDatum := ρ }
  have hgroup : D'.SatisfiesGroupAxioms :=
    ⟨hD.building, hD.boundedSubgroups, hD.affineStructure,
      ⟨hD.affineRootSystem.rootReflections, hD.affineRootSystem.apartmentAxioms,
        hD.affineRootSystem.compatibleApartmentFacets⟩,
      ⟨hD.rootGroupAction.halfApartmentFixers, hD.rootGroupAction.zeroFixerGenerators,
        hD.rootGroupAction.rootZeroFixers⟩,
      hD.titsSystem, hD.iwahoriDecomposition, hM, hQ⟩
  let refl := KPBuildingDatum.BuildingEquivalence.refl D
  refine ⟨D', hgroup, ?_, ⟨⟨refl.equiv, refl.isBuildingIso, refl.isBuildingIso_symm,
    refl.equivariant⟩⟩⟩
  have hRef : D'.IsSpecialTorusInChart 1 i f :=
    ⟨hT, hc, by simpa only [innerIso_one_hom, Category.comp_id] using hf, hi⟩
  have hApt : D'.HasUnramifiedApartmentComparison C Γ H.embedding :=
    hasUnramifiedApartmentComparison D' hD.building i f hf hT hc hGK hi A Z h6 hA H
  have hrange : Set.range H.embedding = {y | ∀ σ : 𝕂 ≃ₐ[F] 𝕂, Γ.action σ y = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩ σ
      exact H.fixed σ x
    · exact H.surjective_fixed y
  have hModels : D'.HasUnramifiedModelComparison C H.embedding E := by
    let : Algebra ↥𝒪[F] (fixedFieldIntegers F) := Valuation.HasExtension.instAlgebraInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
    let : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) 𝕂 :=
      Valuation.HasExtension.instIsScalarTowerInteger
        (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
    intro Ω _
    let N := (M.model Ω).baseChange (fixedFieldIntegers F) 𝕂
    refine ⟨N, hfull Ω, hneutral Ω, ⟨⟨Iso.refl _, ?_⟩⟩, ⟨⟨Iso.refl _, ?_⟩⟩, ?_, ?_⟩
    · simp
      rfl
    · simp
      rfl
    · exact (hM.full_points Ω).symm.trans
        ((M.model Ω).full.integralPoints_eq_comap_baseChangeUnramified.trans
          (congrArg (fun J => J.comap (rationalExtend F 𝕂 G)) (hfull Ω)))
    · exact (hM.neutral_points Ω).symm.trans
        ((M.model Ω).neutral.integralPoints_eq_comap_baseChangeUnramified.trans
          (congrArg (fun J => J.comap (rationalExtend F 𝕂 G)) (hneutral Ω)))
  exact ⟨T, i, f, hRef, hGK, A, Z, h6, hA,
    H.embedding, H.injective, H.equivariant, hrange, hApt, E, hModels⟩

/-- Group-valid KP building data admit a replacement satisfying all four
unramified descent clauses, with the identical reduced building. -/
theorem unramifiedDescentOfGroupAxioms : UnramifiedDescentOfGroupAxiomsStatement.{u} :=
  fun _ D hD => exists_descended_datum D hD

end Langlands.Geometry.Building
