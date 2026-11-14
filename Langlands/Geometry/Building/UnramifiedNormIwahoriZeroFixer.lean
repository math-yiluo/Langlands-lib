import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.UnramifiedCompatibleZeroDatum
import Langlands.Geometry.Building.UnramifiedTorusZeroIntersection
import Langlands.Geometry.Building.UnramifiedZeroNormalizerComparison
import Langlands.Geometry.Building.GenericApartmentFixer
import Langlands.Geometry.Building.IntegerCentralizerStabilizer

/-! # The norm Iwahori as the whole-apartment zero fixer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    [IsAffineHom H.X.hom]
    (E : UnramifiedZeroDatum F H) (B : MaximalUnramified.BuildingData F H)

omit [IsAffineHom H.X.hom] in
/-- The prescribed integer valuation and fixed-field valuation have the same
unit character values on the actual zero subgroup. -/
theorem zeroPoints_le_integerCharacterValuationKernel :
    E.zeroPoints ≤ characterValuationKernel (MaximalUnramified.valuation F) H := by
  intro g hg
  have h := E.zeroPoints_le_characterValuationKernel hg
  rw [mem_characterValuationKernel] at h ⊢
  intro χ
  exact (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mpr (h χ)

/-- A representative of the actual apartment centralizer has the same zero
norm image as the original centralizer datum. -/
theorem centralizerTorusImage_zero_eq_torusIwahoriImage
    (hZ : IsTorus B.centralizer.Z)
    (hE : (torusCentralizer B.i).IsRepresentedBy E.i) :
    B.centralizerTorusImage hZ 0 =
      E.torusIwahori.map (rationalPoints.map E.i) := by
  let e : E.T.toGrp ≅ B.centralizer.Z :=
    hE.isoOfIsRepresentedBy B.centralizer.isRepresentedBy
  have he : e.hom ≫ B.centralizer.j = E.i :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
      hE B.centralizer.isRepresentedBy
  rw [B.centralizerTorusImage_eq_map_iso hZ E.T
    E.isMaximallySplitMaximalTorus.1.1 e 0,
    localTorusFiltration_zero F E.L E.T
      E.isMaximallySplitMaximalTorus.1.1 E.isSplitTorus,
    Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro t
  simpa only [MonoidHom.comp_apply, rationalPoints.map_apply,
    Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : E.T.toGrp ⟶ H => t ≫ f.hom.hom) he

set_option maxHeartbeats 1000000 in
/-- In canonical zero points, the pointwise fixer of the whole apartment
is exactly the image of the actual centralizer's norm Iwahori. -/
theorem wholeApartmentZeroFixer_eq_centralizerTorusImage
    (hZ : IsTorus B.centralizer.Z) :
    E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ) =
      B.centralizerTorusImage hZ 0 := by
  let E' := E.withApartmentTorus B
  have hE : (torusCentralizer B.i).IsRepresentedBy E'.i :=
    E.withApartmentTorus_isRepresentedBy B
  let e : E'.T.toGrp ≅ B.centralizer.Z :=
    hE.isoOfIsRepresentedBy B.centralizer.isRepresentedBy
  have he : e.hom ≫ B.centralizer.j = E'.i :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
      hE B.centralizer.isRepresentedBy
  have hemap (t : rationalPoints E'.T.toGrp) :
      rationalPoints.map B.centralizer.j (rationalPoints.map e.hom t) =
        rationalPoints.map E'.i t := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : E'.T.toGrp ⟶ H => t ≫ f.hom.hom) he
  have heinv (t : rationalPoints E'.T.toGrp) :
      rationalPoints.map e.inv (rationalPoints.map e.hom t) = t := by
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  have hinj : Function.Injective B.apartmentMap :=
    B.apartment.apartmentMap_injective B.isConnectedReductive B.isMaximalSplitTorus
  rw [E'.centralizerTorusImage_zero_eq_torusIwahoriImage B hZ hE]
  apply le_antisymm
  · intro g hg
    have hc : g ∈ centralizerPoints B.i := by
      apply B.apartment.pointwiseFixer_apartment_le_centralizerPoints
        B.isConnectedReductive B.isMaximalSplitTorus
      have hgfix := hg.2
      change g ∈ B.apartment.pointwiseFixer
        (B.apartment.apartmentMap '' Set.univ) at hgfix
      simpa only [Set.image_univ] using hgfix
    rw [← torusCentralizer_carrier_base, ← hE.2] at hc
    obtain ⟨t, ht⟩ := hc
    change rationalPoints.map E'.i t = g at ht
    have hz : rationalPoints.map e.hom t ∈
        characterValuationKernel (MaximalUnramified.valuation F) B.centralizer.Z := by
      apply B.mem_characterValuationKernel_of_mem_oneStabilizer hinj
        (x := Classical.arbitrary B.Apartment)
      constructor
      · rw [hemap, ht]
        exact E.zeroPoints_le_integerCharacterValuationKernel hg.1
      · rw [hemap, ht]
        exact B.apartment.mem_pointwiseFixer.1 hg.2 _
          ⟨Classical.arbitrary B.Apartment, Set.mem_univ _, rfl⟩
    have htint : t ∈ characterValuationKernel
        (MaximalUnramified.valuation F) E'.T.toGrp := by
      have h := map_characterValuationKernel_le
        (MaximalUnramified.valuation F) e.inv
        ⟨rationalPoints.map e.hom t, hz, rfl⟩
      rwa [heinv] at h
    have htfixed : t ∈ characterValuationKernel (fixedFieldValuation F) E'.T.toGrp := by
      rw [mem_characterValuationKernel] at htint ⊢
      intro χ
      exact (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mp (htint χ)
    have htzero : rationalPoints.map E'.i t ∈ E'.zeroPoints := by
      rw [E.withApartmentTorus_zeroPoints B, ht]
      exact hg.1
    have htIw : t ∈ E'.torusIwahori := by
      rw [← E'.zeroPoints_comap_inf_characterValuationKernel_eq_torusIwahori
        B.isMaximalSplitTorus.isSplitSubtorus hE]
      exact ⟨htzero, htfixed⟩
    exact ⟨t, htIw, ht⟩
  · rintro g ⟨t, ht, rfl⟩
    constructor
    · rw [← E.withApartmentTorus_zeroPoints B]
      exact E'.map_torusIwahori_le_zeroPoints ⟨t, ht, rfl⟩
    · apply B.apartment.mem_pointwiseFixer.2
      rintro _ ⟨x, _, rfl⟩
      have hz : rationalPoints.map e.hom t ∈ characterValuationKernel
          (MaximalUnramified.valuation F) B.centralizer.Z :=
        map_characterValuationKernel_le (MaximalUnramified.valuation F) e.hom
          ⟨t, E'.torusIwahori_le_integerCharacterValuationKernel ht, rfl⟩
      rw [← hemap]
      exact B.apartment.mem_reducedFixer.1
        (B.isOmegaCompatible.map_mem_reducedFixer hz x)

/-- Identify the whole-apartment zero fixer with the actual norm-Iwahori
image while preserving its ambient rational point. -/
def wholeApartmentZeroFixerEquiv (hZ : IsTorus B.centralizer.Z) :
    ↥(E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ≃*
      ↥(B.centralizerTorusImage hZ 0) :=
  MulEquiv.subgroupCongr (E.wholeApartmentZeroFixer_eq_centralizerTorusImage B hZ)

end Langlands.Geometry.Building.UnramifiedZeroDatum
