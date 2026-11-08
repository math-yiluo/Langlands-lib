import Langlands.Geometry.Building.AffineTitsRealizationBuilding
import Langlands.Geometry.Building.RealizationCoordinateAction
import Langlands.Group.TitsRestrictedApartments
import Langlands.Group.TitsRestrictedAutomorphisms

/-! # The polysimplicial realization given by the restricted Tits building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}

namespace IsBuildingTitsSystem

variable (hT : P.IsBuildingTitsSystem Ca π Sgen)
include hT

theorem finite_sgen : Finite Sgen :=
  hT.finite.to_subtype

/-- The facets of `B(G)` correspond to the admissible parabolic subgroups of
`G(F)^0` through their stabilizers (KP Axiom 4.1.9). -/
def facetAdmissibleEquiv :
    BuildingFacet P.toValuationBuildingData ≃
      {Q : Subgroup P.zeroSubgroup //
        IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q} :=
  (Equiv.Set.univ _).symm.trans (hT.bijOn_facetZeroStabilizer.equiv _)

@[simp] theorem coe_facetAdmissibleEquiv (Fc : BuildingFacet P.toValuationBuildingData) :
    (hT.facetAdmissibleEquiv Fc : Subgroup P.zeroSubgroup) = P.facetZeroStabilizer Fc :=
  rfl

theorem isAdmissibleParabolic_facetZeroStabilizer
    (Fc : BuildingFacet P.toValuationBuildingData) :
    IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen (P.facetZeroStabilizer Fc) :=
  hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fc)

/-- The polysimplicial realization of `B(G)` by the restricted building of the
Tits system (KP Proposition 1.5.18(3) and Axiom 4.1.9): one simplicial factor
for each irreducible component of `Sgen`. -/
def titsRealization : P.toValuationBuildingData.PolysimplicialRealization :=
  haveI := hT.finite_sgen
  { index := Component Sgen
    V := hT.isTitsSystem.ComponentVertex
    complex := hT.isTitsSystem.restrictedComplex
    realize := (hT.isTitsSystem.restrictedFacetOrderIso.symm.toEquiv.trans OrderDual.ofDual).trans
      hT.facetAdmissibleEquiv.symm }

/-- The facet of the complex realizing a facet of `B(G)` is the product of the
component simplices of its stabilizer. -/
theorem coe_titsRealization_realize_symm (Fc : BuildingFacet P.toValuationBuildingData) :
    ((hT.titsRealization.realize.symm Fc : hT.titsRealization.complex.facets) :
        Set (∀ i, hT.titsRealization.V i)) =
      hT.isTitsSystem.restrictedBox (P.facetZeroStabilizer Fc) :=
  rfl

/-- The realization is compatible with the original facet incidence. -/
theorem titsRealization_isFaceCompatible : hT.titsRealization.IsFaceCompatible := by
  have := hT.finite_sgen
  intro Fc Fc'
  obtain ⟨E, rfl⟩ := hT.titsRealization.realize.symm.surjective Fc
  obtain ⟨E', rfl⟩ := hT.titsRealization.realize.symm.surjective Fc'
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hT.facetPrecedes_iff,
    hT.coe_titsRealization_realize_symm, hT.coe_titsRealization_realize_symm]
  exact hT.isTitsSystem.restrictedBox_subset_iff (hT.isAdmissibleParabolic_facetZeroStabilizer E)

/-- Each apartment of `B(G)` realizes a restricted Tits apartment. -/
theorem exists_titsRealization_apartmentComplex_eq {Y : Set P.ReducedBuilding}
    (hY : P.IsApartment Y) :
    ∃ a : P.zeroSubgroup, hT.titsRealization.apartmentComplex Y =
      (haveI := hT.finite_sgen; hT.isTitsSystem.restrictedApartmentBoxes a) := by
  have := hT.finite_sgen
  obtain ⟨h, rfl⟩ := hY
  have hmem : P.facetZeroStabilizer ''
      {Fc | Fc.val ⊆ h • P.apartmentImage} ∈ P.apartmentFacetStabilizers := ⟨h, rfl⟩
  rw [hT.apartmentFacetStabilizers_eq] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, ?_⟩
  ext Fs
  constructor
  · rintro ⟨hFs, hsub⟩
    let E := hT.titsRealization.realize ⟨Fs, hFs⟩
    have hFsE : Fs = hT.isTitsSystem.restrictedBox (P.facetZeroStabilizer E) := by
      rw [← hT.coe_titsRealization_realize_symm, Equiv.symm_apply_apply]
    refine ⟨P.facetZeroStabilizer E, ?_, hFsE⟩
    rw [ha]
    exact ⟨E, hsub, rfl⟩
  · rintro ⟨Q, hQ, rfl⟩
    rw [ha] at hQ
    obtain ⟨E, hE, rfl⟩ := hQ
    refine ⟨(hT.titsRealization.realize.symm E).2, ?_⟩
    have : (⟨hT.isTitsSystem.restrictedBox (P.facetZeroStabilizer E),
        (hT.titsRealization.realize.symm E).2⟩ : hT.titsRealization.complex.facets) =
        hT.titsRealization.realize.symm E := Subtype.ext rfl
    rw [this, Equiv.apply_symm_apply]
    exact hE

/-- Every apartment of the realization is polysimplicial. -/
theorem isPolysimplicial_titsRealization_apartmentComplex {Y : Set P.ReducedBuilding}
    (hY : P.IsApartment Y) :
    AbstractBuilding.IsPolysimplicial (hT.titsRealization.apartmentComplex Y) := by
  have := hT.finite_sgen
  obtain ⟨a, ha⟩ := hT.exists_titsRealization_apartmentComplex_eq hY
  rw [ha]
  exact hT.isTitsSystem.isPolysimplicial_restrictedApartmentBoxes a

/-- The building clause for the restricted-building realization, with
singleton admissibility retained. -/
theorem titsRealization_isBuilding (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s}) :
    AbstractBuilding.IsBuilding hT.titsRealization.complex hT.titsRealization.apartments :=
  hT.realization_isBuilding _ hT.titsRealization_isFaceCompatible hadm
    fun _ hY => hT.isPolysimplicial_titsRealization_apartmentComplex hY

/-- Distinct facets of `B(G)` give distinct products of component simplices. -/
theorem restrictedBox_facetZeroStabilizer_eq_iff
    (E E' : BuildingFacet P.toValuationBuildingData) :
    hT.isTitsSystem.restrictedBox (P.facetZeroStabilizer E) =
        hT.isTitsSystem.restrictedBox (P.facetZeroStabilizer E') ↔ E = E' := by
  constructor
  · intro he
    exact hT.titsRealization.realize.symm.injective (Subtype.ext he)
  · rintro rfl
    rfl

section Action

variable [P.zeroSubgroup.Normal]

omit hT in
/-- Stabilizers in `G(F)^0` of translated facets are conjugate stabilizers. -/
theorem facetZeroStabilizer_translate (g : rationalPoints G)
    (Fc : BuildingFacet P.toValuationBuildingData) :
    P.facetZeroStabilizer (P.toValuationBuildingData.facetTranslateEquiv g Fc) =
      (P.facetZeroStabilizer Fc).map (MulAut.conjNormal g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, facetZeroStabilizer, facetZeroStabilizer, mem_zeroStabilizerIn,
    mem_zeroStabilizerIn, MulAut.conjNormal_symm_apply,
    P.toValuationBuildingData.facetTranslateEquiv_val, mul_smul, mul_smul, inv_smul_eq_iff]

/-- Conjugation by a rational point preserves the admissible parabolic
subgroups of `G(F)^0`. -/
theorem isAdmissibleParabolic_map_conjNormal_iff (g : rationalPoints G)
    (Q : Subgroup P.zeroSubgroup) :
    IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen
        (Q.map (MulAut.conjNormal g).toMonoidHom) ↔
      IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q := by
  constructor
  · intro hQ
    obtain ⟨E, -, hE⟩ := hT.bijOn_facetZeroStabilizer.surjOn hQ
    have hQE : Q = P.facetZeroStabilizer (P.toValuationBuildingData.facetTranslateEquiv g⁻¹ E) := by
      rw [facetZeroStabilizer_translate, hE, map_inv, MulAut.inv_def, map_symm_map]
    rw [hQE]
    exact hT.isAdmissibleParabolic_facetZeroStabilizer _
  · intro hQ
    obtain ⟨E, -, rfl⟩ := hT.bijOn_facetZeroStabilizer.surjOn hQ
    rw [← facetZeroStabilizer_translate]
    exact hT.isAdmissibleParabolic_facetZeroStabilizer _

/-- The original rational-point action is polysimplicial on the realization
(KP Axiom 4.1.1), assuming that `G(F)^0` is normal in `G(F)`. -/
theorem titsRealization_isPolysimplicialAction : hT.titsRealization.IsPolysimplicialAction := by
  have := hT.finite_sgen
  rw [hT.titsRealization.isPolysimplicialAction_iff_respectsCoordinateFibers
    hT.titsRealization_isFaceCompatible]
  intro g
  obtain ⟨σ, hσ⟩ :=
    hT.isTitsSystem.exists_componentPerm (hT.isAdmissibleParabolic_map_conjNormal_iff g)
  refine ⟨σ, ?_⟩
  have he : hT.isTitsSystem.autVertexEquiv hσ =
      hT.titsRealization.vertexTranslateEquiv hT.titsRealization_isFaceCompatible g := by
    apply hT.titsRealization.vertexTranslateEquiv_unique
    intro Fc Fc'
    obtain ⟨E, rfl⟩ := hT.titsRealization.realize.symm.surjective Fc
    obtain ⟨E', rfl⟩ := hT.titsRealization.realize.symm.surjective Fc'
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change hT.isTitsSystem.restrictedBox (P.facetZeroStabilizer E') =
        (hT.isTitsSystem.autVertexEquiv hσ) ''
          hT.isTitsSystem.restrictedBox (P.facetZeroStabilizer E) ↔ _
    rw [← hT.isTitsSystem.restrictedBox_map hσ, ← facetZeroStabilizer_translate,
      hT.restrictedBox_facetZeroStabilizer_eq_iff, Subtype.ext_iff,
      P.toValuationBuildingData.facetTranslateEquiv_val]
    rfl
  rw [← he]
  exact hT.isTitsSystem.respectsCoordinateFibers_autVertexEquiv hσ

/-- KP Axiom 4.1.1 for the restricted-building realization. Singleton
admissibility, normality of `G(F)^0`, the torus correspondence and the
normalizer stabilizer remain explicit hypotheses. -/
theorem satisfiesBuildingAxiom_titsRealization
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s})
    (htorus : P.HasTorusApartmentCorrespondence)
    (hnorm : P.HasNormalizerApartmentStabilizer) :
    P.SatisfiesBuildingAxiom hT.titsRealization where
  faceCompatible := hT.titsRealization_isFaceCompatible
  isBuilding := hT.titsRealization_isBuilding hadm
  polysimplicialAction := hT.titsRealization_isPolysimplicialAction
  torusApartmentCorrespondence := htorus
  normalizerApartmentStabilizer := hnorm

end Action

end IsBuildingTitsSystem

section Affine

variable (P) [P.normalizerZero.Normal] [P.zeroSubgroup.Normal]

/-- For the literal affine Tits datum, the affine-root and chamber hypotheses
discharge singleton admissibility. -/
theorem satisfiesBuildingAxiom_affineTitsRealization
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (hA : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    (hCa : AffineRootSystem.IsChamber P.affineRoots Ca)
    (hT : P.IsBuildingTitsSystem Ca P.affineTitsProjection (P.chamberSimpleInAffinePart e Ca))
    (htorus : P.HasTorusApartmentCorrespondence)
    (hnorm : P.HasNormalizerApartmentStabilizer) :
    P.SatisfiesBuildingAxiom hT.titsRealization :=
  hT.satisfiesBuildingAxiom_titsRealization
    (fun _ hs => P.isAdmissibleType_singleton_chamberSimpleInAffinePart e hA hCa hs) htorus hnorm

end Affine

end Langlands.Geometry.Building.ParahoricBuildingData
