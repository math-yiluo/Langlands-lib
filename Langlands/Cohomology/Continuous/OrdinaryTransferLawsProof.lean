import Langlands.Cohomology.Continuous.OrdinaryTransferLawsStatement
import Langlands.Cohomology.Tate.PositiveCorestriction
import Langlands.Cohomology.Tate.TowerTransitivity

noncomputable section

universe u

open CategoryTheory
open Langlands.Tate

namespace Langlands.Continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G]

/-- The actual ordinary corestriction is the coset norm under the invariant description of H⁰. -/
@[reassoc]
lemma ordinaryCorestriction_H0Iso (H : Subgroup G) [Fintype (G ⧸ H)]
    (A : Rep.{u} R G) :
    ordinaryCohomologyCorestriction H A 0 ≫ (groupCohomology.H0Iso A).hom =
      (groupCohomology.H0Iso (Rep.res H.subtype A)).hom ≫
        ModuleCat.ofHom (cosetNorm H A) := by
  apply (cancel_epi (groupCohomology.π (Rep.res H.subtype A) 0)).mp
  apply (cancel_mono (groupCohomology.shortComplexH0 A).f).mp
  change ((groupCohomology.inhomogeneousCochains (Rep.res H.subtype A)).homologyπ 0 ≫
    HomologicalComplex.homologyMap (ordinaryCorestrictionCochainMap H A) 0 ≫
      (groupCohomology.H0Iso A).hom) ≫ _ = _
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  simp only [Category.assoc, groupCohomology.π_comp_H0Iso_hom,
    groupCohomology.π_comp_H0Iso_hom_assoc,
    groupCohomology.cocyclesIso₀_hom_comp_f]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  apply (cancel_epi (groupCohomology.cocyclesIso₀ (Rep.res H.subtype A)).inv).mp
  simp only [← Category.assoc, groupCohomology.cocyclesIso₀_inv_comp_iCocycles,
    Iso.inv_hom_id, Category.id_comp]
  ext a
  exact ordinaryCorestrictionCochainMap_zero H A a

/-- Ordinary restriction in degree zero is the inclusion of invariant submodules. -/
@[reassoc]
lemma ordinaryRestriction_H0Iso (H : Subgroup G) (A : Rep.{u} R G) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 0 ≫
        (groupCohomology.H0Iso (Rep.res H.subtype A)).hom =
      (groupCohomology.H0Iso A).hom ≫ ModuleCat.ofHom (invariantRestriction H A) := by
  apply (cancel_mono (groupCohomology.shortComplexH0 (Rep.res H.subtype A)).f).mp
  simp only [Category.assoc, groupCohomology.map_H0Iso_hom_f]
  rfl

/-- The tower's ordinary degree-zero coordinate map is identity on the underlying invariants. -/
@[reassoc]
lemma ordinaryTowerReindex_H0Iso (K H : Subgroup G) (h : K ≤ H) (A : Rep.{u} R G) :
    groupCohomology.map (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
        (towerCoefficientIso h A).hom 0 ≫
      (groupCohomology.H0Iso (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype A))).hom =
    (groupCohomology.H0Iso (Rep.res K.subtype A)).hom ≫
      ModuleCat.ofHom (reindexInvariants (Subgroup.subgroupOfEquivOfLe h).symm
        (towerCoefficientIso h A).hom) := by
  apply (cancel_mono
    (groupCohomology.shortComplexH0 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype A))).f).mp
  simp only [Category.assoc, groupCohomology.map_H0Iso_hom_f]
  rfl

/-- The index identity on ordinary H⁰ follows from its invariant coset-norm formula. -/
lemma ordinaryCorestriction_index_zero (H : Subgroup G) [Fintype (G ⧸ H)]
    (A : Rep.{u} R G) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 0 ≫
        ordinaryCohomologyCorestriction H A 0 = H.index • 𝟙 (groupCohomology A 0) := by
  apply (cancel_mono (groupCohomology.H0Iso A).hom).mp
  rw [Category.assoc, ordinaryCorestriction_H0Iso, ordinaryRestriction_H0Iso_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change cosetNorm H A (invariantRestriction H A ((groupCohomology.H0Iso A).hom x)) =
    (groupCohomology.H0Iso A).hom (H.index • x)
  rw [map_nsmul]
  exact cosetNorm_invariantRestriction H _

/-- Transitivity on ordinary H⁰ follows from composition of the two coset norms. -/
lemma ordinaryCorestriction_tower_zero (K H : Subgroup G) (h : K ≤ H)
    [Fintype (G ⧸ K)] [Fintype (G ⧸ H)] [Fintype (H ⧸ K.subgroupOf H)]
    (A : Rep.{u} R G) :
    ordinaryCohomologyCorestriction K A 0 =
      groupCohomology.map (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
          (towerCoefficientIso h A).hom 0 ≫
        ordinaryCohomologyCorestriction (K.subgroupOf H) (Rep.res H.subtype A) 0 ≫
        ordinaryCohomologyCorestriction H A 0 := by
  apply (cancel_mono (groupCohomology.H0Iso A).hom).mp
  simp only [Category.assoc, ordinaryCorestriction_H0Iso, ordinaryCorestriction_H0Iso_assoc,
    ordinaryTowerReindex_H0Iso_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact cosetNorm_trans h A ((groupCohomology.H0Iso (Rep.res K.subtype A)).hom x)

variable [Fintype G]

/-- Positive ordinary restriction followed by corestriction multiplies by the index. -/
lemma ordinaryCorestriction_index_pos (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]
    (A : Rep.{u} R G) (q : ℕ) [NeZero q] :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) q ≫
        ordinaryCohomologyCorestriction H A q = H.index • 𝟙 (groupCohomology A q) := by
  have ht : ModuleCat.ofHom (restriction H A q) ≫ ModuleCat.ofHom (corestriction H A q) =
      H.index • 𝟙 (tateCohomology A q) := by
    ext x
    exact corestriction_restriction H A q x
  rw [restriction_groupCohomology, corestriction_groupCohomology] at ht
  apply (cancel_mono ((TateCohomology.isoGroupCohomology q).app A).inv).mp
  apply (cancel_epi ((TateCohomology.isoGroupCohomology q).app A).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.comp_nsmul,
    Preadditive.nsmul_comp, Category.id_comp, Category.comp_id, Iso.hom_inv_id] using ht

/-- The positive ordinary tower law retains the canonical change of subgroup coordinates. -/
lemma ordinaryCorestriction_tower_pos (K H : Subgroup G) (h : K ≤ H)
    [Fintype K] [Fintype H] [Fintype (K.subgroupOf H)]
    [Fintype (G ⧸ K)] [Fintype (G ⧸ H)] [Fintype (H ⧸ K.subgroupOf H)]
    (A : Rep.{u} R G) (q : ℕ) [NeZero q] :
    ordinaryCohomologyCorestriction K A q =
      groupCohomology.map (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
          (towerCoefficientIso h A).hom q ≫
        ordinaryCohomologyCorestriction (K.subgroupOf H) (Rep.res H.subtype A) q ≫
        ordinaryCohomologyCorestriction H A q := by
  have ht : ModuleCat.ofHom (corestriction K A q) =
      (towerReindex h A q).hom ≫
        ModuleCat.ofHom (corestriction (K.subgroupOf H) (Rep.res H.subtype A) q) ≫
        ModuleCat.ofHom (corestriction H A q) := by
    ext x
    exact corestriction_trans h A q x
  change ModuleCat.ofHom (corestriction K A q) =
    reindex (Subgroup.subgroupOfEquivOfLe h).symm (towerCoefficientIso h A).hom q ≫ _ at ht
  rw [reindex_groupCohomology, corestriction_groupCohomology,
    corestriction_groupCohomology, corestriction_groupCohomology] at ht
  apply (cancel_mono ((TateCohomology.isoGroupCohomology q).app A).inv).mp
  apply (cancel_epi
    ((TateCohomology.isoGroupCohomology q).app (Rep.res K.subtype A)).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, MulEquiv.symm_symm] using ht

/-- The actual ordinary corestriction satisfies index and tower laws in every natural degree. -/
theorem ordinaryTransferLaws : OrdinaryTransferLaws.{u} := by
  constructor
  · intro R G _ _ _ H _ _ A q
    cases q with
    | zero => exact ordinaryCorestriction_index_zero H A
    | succ n => exact ordinaryCorestriction_index_pos H A (n + 1)
  · intro R G _ _ _ K H h _ _ _ _ _ _ A q
    cases q with
    | zero => exact ordinaryCorestriction_tower_zero K H h A
    | succ n => exact ordinaryCorestriction_tower_pos K H h A (n + 1)

end Langlands.Continuous
