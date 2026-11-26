import Langlands.Geometry.Building.FacetParabolicComparisonStatement
import Langlands.Geometry.Building.AffineIwahoriTitsProof
import Langlands.Geometry.Building.AffineIwahoriTitsBuildingProof
import Langlands.Geometry.Building.ChamberParahoricConstancy
import Langlands.Geometry.Building.ZeroFixerNormalizerReduction

/-! # The actual common-chamber facet-parabolic comparison -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme
open Langlands.Group.TitsSystem

namespace Langlands.Geometry.Building

open AffineRootSystem

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} [P.normalizerZero.Normal]

/-- KP Proposition 7.5.5 for one face of the chamber of the actual Iwahori–Tits datum. -/
private theorem facetParabolicComparisonWith
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C Fa : Set P.Apartment} (hC : IsChamber P.affineRoots C)
    (hFa : IsFaceOf P.affineRoots Fa C)
    {e : P.affinePart ≃* affineWeylGroup P.affineRoots}
    (hW : P.AffineIwahoriTitsWith C e) :
    P.FacetParabolicComparisonWith C Fa e := by
  obtain ⟨c, _, rfl⟩ := hC
  obtain ⟨x, rfl⟩ := hFa.1
  have hx : x ∈ facetClosure P.affineRoots c :=
    facetClosure_subset_facetClosure_iff.1 (isFaceOf_facet_iff_facetClosure_subset.1 hFa)
  let X := P.facetSimpleInAffinePart e (facet P.affineRoots c) (facet P.affineRoots x)
  have hIndex (n : P.normalizerInZero) :
      (n : P.zeroSubgroup) ∈ P.zeroStabilizerIn (P.apartmentMap '' facet P.affineRoots x) ↔
        P.affineTitsProjection n ∈ Subgroup.closure X := by
    rw [← SetLike.mem_coe, coe_zeroStabilizerIn_facet hA hW hx]
    exact hW.tits.mem_standardParabolic_iff_of_mem_cell (coe_mem_cell n)
  have hNormalizer (n : P.normalizerInZero) :
      normalizerInZeroPoint n ∈ P.normalizerStabilizer (facet P.affineRoots x) ↔
        P.affineTitsProjection n ∈ Subgroup.closure X := by
    rw [← hIndex n, P.mem_zeroStabilizerIn, ← coe_normalizerInZeroPoint,
      normalizer_smul_image_apartmentMap,
      (P.apartmentMap_injective_of_rankOne hA P.hasRankOneFactorization_actual).image_injective.eq_iff,
      P.mem_normalizerStabilizer]
  have hFaZero := P.parahoric_le_zeroSubgroup hA (facet P.affineRoots x)
  refine ⟨hFa, hFaZero, ?_, ?_⟩
  · change (Subgroup.closure X).map P.affinePart.subtype = _
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨n, rfl⟩ := hW.tits.surjective v
      exact ⟨normalizerInZeroPoint n, ⟨(P.normalizerInZeroEquiv n).property,
        (hNormalizer n).2 hv⟩, (P.affineTitsProjection_coe n).symm⟩
    · rintro ⟨n, ⟨hnZero, hnFa⟩, rfl⟩
      let m := P.normalizerInZeroEquiv.symm ⟨n, hnZero⟩
      exact ⟨P.affineTitsProjection m, (hNormalizer m).1 hnFa, P.affineTitsProjection_coe m⟩
  · have hLe : P.parahoric (facet P.affineRoots c) ≤ P.parahoric (facet P.affineRoots x) := by
      rw [P.parahoric_eq_parahoricAt_of_isFacet hA (isFacet_facet _ c) (mem_facet_self _ c),
        P.parahoric_eq_parahoricAt_of_isFacet hA (isFacet_facet _ x) (mem_facet_self _ x)]
      exact sup_le_sup_left
        (P.apartment.sharpFixer_singleton_le_of_mem_facetClosure hA.mem_or_two_smul_mem hx) _
    have hB : P.parahoricInZero (facet P.affineRoots c) ≤
        P.parahoricInZero (facet P.affineRoots x) := fun _ hg => hLe hg
    have hFix : P.parahoricInZero (facet P.affineRoots x) ≤
        P.zeroStabilizerIn (P.apartmentMap '' facet P.affineRoots x) := by
      intro g hg
      exact P.mem_zeroStabilizerIn.2 (smul_image_apartmentMap_eq
        (P.mem_zeroFixer.1 (P.parahoric_le_zeroFixer hA _ hg)).2)
    change (P.parahoricInZero (facet P.affineRoots x) : Set P.zeroSubgroup) =
      standardParabolic (P.parahoricInZero (facet P.affineRoots c)) P.affineTitsProjection X
    refine hW.tits.coe_eq_standardParabolic hB (fun n hn => (hIndex n).1 (hFix hn)) ?_
    intro v hv
    refine exists_rep_mem_of_mem_closure (fun s hs => ?_) hv
    change e s ∈ facetSimpleReflections _ _ _ at hs
    obtain ⟨ψ, hψ, a, ha, hs⟩ := hs
    obtain ⟨n, hn, hnAction⟩ := P.exists_sharpFixer_normalizer_eq_affineReflection hA
      (simpleAffineRoots_subset _ _ hψ.1) hψ.2 ha
    have hnP := P.sharpFixer_le_parahoric _ hn
    let m : P.normalizerZeroComponent := ⟨n, hFaZero hnP⟩
    refine ⟨P.normalizerInZeroEquiv.symm m, e.injective (Subtype.ext ?_), hnP⟩
    exact (hW.action_compatible m).trans (hnAction.trans hs.symm)

end ParahoricBuildingData

/-- The actual common-chamber form of the facet-parabolic comparison
(Kaletha–Prasad, Proposition 7.5.5). -/
theorem facetParabolicComparison : FacetParabolicComparisonStatement.{u} := by
  intro F _ _ _ _ G _ P hA C F₁ F₂ hC hF₁ hF₂
  obtain ⟨hN, hG, e, hW⟩ := affineIwahoriTits F G P hA C hC
  let : P.normalizerZero.Normal := hN
  exact ⟨hN, hG, e, hW,
    ParahoricBuildingData.facetParabolicComparisonWith hA hC hF₁ hW,
    ParahoricBuildingData.facetParabolicComparisonWith hA hC hF₂ hW⟩

end Langlands.Geometry.Building
