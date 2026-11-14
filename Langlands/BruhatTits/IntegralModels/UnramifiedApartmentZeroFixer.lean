import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralTorusIwahori
import Langlands.Geometry.Building.GenericApartmentFixer
import Langlands.Geometry.Building.IntegerCentralizerStabilizer
import Langlands.Geometry.Building.UnramifiedTorusZeroIntersection

/-! # The zero fixer of the whole unramified apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (E : UnramifiedZeroDatum F G)
    (hE : (torusCentralizer C.i).IsRepresentedBy E.i)

include hE in
/-- Fixing one apartment point in the ambient one-kernel forces a compatible
torus point into its own fixed-field character-valuation kernel. -/
theorem compatibleTorus_mem_characterValuationKernel_of_mem_oneStabilizer
    {t : rationalPoints E.T.toGrp} {x : C.Apartment}
    (ht : rationalPoints.map E.i t ∈ C.oneStabilizer (C.apartmentMap x)) :
    t ∈ characterValuationKernel (fixedFieldValuation F) E.T.toGrp := by
  let e := hE.isoOfIsRepresentedBy C.centralizer.isRepresentedBy
  have he : e.hom ≫ C.centralizer.j = E.i :=
    hE.isoOfIsRepresentedBy_hom_comp C.centralizer.isRepresentedBy
  have hp : rationalPoints.map C.centralizer.j (rationalPoints.map e.hom t) =
      rationalPoints.map E.i t := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : E.T.toGrp ⟶ G => t ≫ f.hom.hom) he
  have hz : rationalPoints.map e.hom t ∈
      characterValuationKernel (MaximalUnramified.valuation F) C.centralizer.Z :=
    C.mem_characterValuationKernel_of_mem_oneStabilizer
      (C.apartment.apartmentMap_injective C.isConnectedReductive C.isMaximalSplitTorus)
      (hp.symm ▸ ht)
  have hback : rationalPoints.map e.inv (rationalPoints.map e.hom t) = t := by
    change (t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = t
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id]
    rfl
  have ht' : t ∈
      characterValuationKernel (MaximalUnramified.valuation F) E.T.toGrp := by
    rw [← hback]
    exact map_characterValuationKernel_le _ e.inv ⟨_, hz, rfl⟩
  rw [mem_characterValuationKernel] at ht' ⊢
  intro χ
  exact (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mp (ht' χ)

set_option maxHeartbeats 800000 in
include hE in
/-- For a compatible torus, the zero points fixing the entire original
apartment are exactly the image of its norm-defined Iwahori subgroup. -/
theorem compatibleApartmentZeroFixer_eq_torusIwahori :
    E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap) =
      E.torusIwahori.map (rationalPoints.map E.i) := by
  apply le_antisymm
  · rintro g ⟨hg0, hgfix⟩
    have hgc : g ∈ centralizerPoints C.i :=
      C.apartment.pointwiseFixer_apartment_le_centralizerPoints
        C.isConnectedReductive C.isMaximalSplitTorus hgfix
    have hrange : (rationalPoints.map E.i).range = centralizerPoints C.i := by
      rw [← SubgroupFunctor.rationalPoints_eq_range hE]
      exact torusCentralizer_carrier_base C.i
    obtain ⟨t, htg⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ hgc)
    have hg1 : g ∈ characterValuationKernel (MaximalUnramified.valuation F) G := by
      have hfixed := E.zeroPoints_le_characterValuationKernel hg0
      rw [mem_characterValuationKernel] at hfixed ⊢
      intro χ
      exact (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mpr (hfixed χ)
    let x : C.Apartment := Classical.choice inferInstance
    have htx : rationalPoints.map E.i t ∈ C.oneStabilizer (C.apartmentMap x) := by
      rw [htg, C.mem_oneStabilizer]
      exact ⟨hg1, C.apartment.mem_pointwiseFixer.1 hgfix _ ⟨x, rfl⟩⟩
    have htker := compatibleTorus_mem_characterValuationKernel_of_mem_oneStabilizer
      C E hE htx
    have htI : t ∈ E.torusIwahori := by
      rw [← E.zeroPoints_comap_inf_characterValuationKernel_eq_torusIwahori
        C.isMaximalSplitTorus.isSplitSubtorus hE]
      refine ⟨?_, htker⟩
      change rationalPoints.map E.i t ∈ E.zeroPoints
      rwa [htg]
    exact ⟨t, htI, htg⟩
  · rintro g ⟨t, ht, rfl⟩
    refine ⟨E.map_torusIwahori_le_zeroPoints ⟨t, ht, rfl⟩, ?_⟩
    have hfix := (map_compatibleTorusIwahori_le_oneFixer C E hE Set.univ
      ⟨t, ht, rfl⟩).2
    simpa only [Set.image_univ] using hfix

/-- The whole-apartment zero fixer and torus Iwahori image are identified
without changing any ambient rational point. -/
def compatibleApartmentZeroFixerEquiv :
    ↥(E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap)) ≃*
      E.torusIwahori.map (rationalPoints.map E.i) :=
  MulEquiv.subgroupCongr (compatibleApartmentZeroFixer_eq_torusIwahori C E hE)

@[simp]
theorem coe_compatibleApartmentZeroFixerEquiv
    (g : ↥(E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap))) :
    (compatibleApartmentZeroFixerEquiv C E hE g : rationalPoints G) = g := rfl

end Langlands.BruhatTits.IntegralModels
