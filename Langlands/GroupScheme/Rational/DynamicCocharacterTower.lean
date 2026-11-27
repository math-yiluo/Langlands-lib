import Langlands.GroupScheme.Rational.GaloisSubgroupTowerTransport
import Langlands.GroupScheme.Torus.CocharacterFieldTransport
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # Dynamic subgroups of cocharacters extended along a tower -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open StarActionFiniteStage MultiplicativeTypeAbsoluteEquivalence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000

private theorem comap_range_comp_iso
    {S : Scheme.{u}} {A B C : GroupScheme S} (i : A ⟶ B) (e : B ≅ C) :
    (SubgroupFunctor.range (i ≫ e.hom)).comap e.hom = SubgroupFunctor.range i := by
  ext U x
  simp only [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range,
    Grp.comp_hom_hom, ← Category.assoc]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, (cancel_mono e.hom.hom.hom).mp hy⟩,
    fun ⟨y, hy⟩ => ⟨y, congrArg (fun z => z ≫ e.hom.hom.hom) hy⟩⟩

private theorem towerBaseChange_range
    {B S K : Scheme.{u}} (b : S ⟶ B) (j : K ⟶ S) (c : K ⟶ B) (h : j ≫ b = c)
    {H G : GroupScheme B} (i : H ⟶ G) :
    SubgroupFunctor.towerBaseChange b j c h G (SubgroupFunctor.range ((baseChange b).map i)) =
      SubgroupFunctor.range ((baseChange c).map i) := by
  unfold SubgroupFunctor.towerBaseChange
  rw [← SubgroupFunctor.range_baseChangeHom, baseChange_map_eq_groupTowerIsoOf b j c h i,
    ← Iso.symm_hom (groupTowerIsoOf b j c h H), SubgroupFunctor.range_iso_comp]
  exact comap_range_comp_iso _ _

section TorusTower

variable {F Q E : Type u} [Field F] [Field Q] [Field E]
  [Algebra F Q] [Algebra F E] [Algebra Q E] [IsScalarTower F Q E]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (t : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap F Q
local notation "c" => algebraBaseMap F E
local notation "j" => algebraBaseMap Q E
local notation "hk" => algebraBaseMap_tower Q E
local notation "TQ" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "tQ" => CategoryTheory.Functor.map (GroupScheme.baseChange b) t
local notation "tE" => CategoryTheory.Functor.map (GroupScheme.baseChange c) t
local notation "eG" => groupTowerIsoOf b j c hk G

private theorem towerExtension_comp_ambient
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T)) :
    (CommGroupScheme.groupHom (cocharacterLattice.towerExtension F Q E T ν) ≫ tE) ≫
      (eG).hom = Dynamic.baseChangeCocharacter j (CommGroupScheme.groupHom ν ≫ tQ) := by
  let eT := towerIsoOf b j T c hk
  let i := groupTowerIsoOf b j c hk T.toGrp
  let ξ := cocharacterLattice.baseChange j (TQ) ν
  have hν : cocharacterLattice.towerExtension F Q E T ν =
      cocharacterLattice.congr eT.symm ξ := rfl
  have he : CommGroupScheme.groupHom (cocharacterLattice.congr eT.symm ξ) =
      CommGroupScheme.groupHom ξ ≫ i.inv := by
    change CommGroupScheme.groupHom ξ ≫ CommGroupScheme.groupHom eT.inv = _
    rw [cocharacterLattice.groupHom_towerIsoOf_inv]
  rw [hν, he, Category.assoc, Category.assoc]
  have hmap : (GroupScheme.baseChange j).map tQ = i.inv ≫ tE ≫ (eG).hom :=
    baseChange_map_eq_groupTowerIsoOf b j c hk t
  rw [← hmap]
  exact ((Dynamic.baseChangeCocharacter_comp_hom j (CommGroupScheme.groupHom ν) (tQ)).trans
    (congrArg (fun z => z ≫ (GroupScheme.baseChange j).map (tQ))
      (cocharacterLattice.groupHom_baseChange_dynamic j (TQ) ν).symm)).symm

/-- The dynamic unipotent subgroup extends through the canonical tower map. -/
theorem unipotent_towerExtension
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T)) :
    Dynamic.unipotent (CommGroupScheme.groupHom (cocharacterLattice.towerExtension F Q E T ν) ≫
      tE) = SubgroupFunctor.towerBaseChange b j c hk G
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ tQ)) := by
  rw [Dynamic.unipotent_eq_comap_of_iso _ (eG), towerExtension_comp_ambient,
    Dynamic.unipotent_baseChange]
  rfl

/-- An equality between the dynamic centralizer and the torus range
persists after extending the cocharacter along the tower. -/
theorem centralizer_towerExtension
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T))
    (h : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tQ) = SubgroupFunctor.range tQ) :
    Dynamic.centralizer (CommGroupScheme.groupHom (cocharacterLattice.towerExtension F Q E T ν) ≫
      tE) = SubgroupFunctor.range tE := by
  have he : Dynamic.centralizer (CommGroupScheme.groupHom
      (cocharacterLattice.towerExtension F Q E T ν) ≫ tE) =
      SubgroupFunctor.towerBaseChange b j c hk G
        (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tQ)) := by
    rw [Dynamic.centralizer_eq_comap_of_iso _ (eG), towerExtension_comp_ambient,
      Dynamic.centralizer_baseChange]
    rfl
  exact he.trans ((congrArg (SubgroupFunctor.towerBaseChange b j c hk G) h).trans
    (towerBaseChange_range b j c hk t))

end TorusTower

section Galois

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (t : T.toGrp ⟶ G)

/-- The unipotent subgroup of the translated cocharacter is the
coefficient transport of the original unipotent subgroup. -/
theorem unipotent_galoisRepresentation
    (σ : E ≃ₐ[F] E)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T)) :
    Dynamic.unipotent (CommGroupScheme.groupHom
      (cocharacterLattice.galoisRepresentation F E T σ ν) ≫
      (GroupScheme.baseChange (algebraBaseMap F E)).map t) =
      SubgroupFunctor.galoisTransport F E G σ
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫
          (GroupScheme.baseChange (algebraBaseMap F E)).map t)) := by
  let b := algebraBaseMap F E
  let a := galoisBaseMap F E σ
  let ha := galoisBaseMap_over F E σ
  let χ := CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map t
  let e := descentBaseChangeIso b a ha G
  change Dynamic.unipotent (transportCocharacter b a ha T.toGrp (CommGroupScheme.groupHom ν) ≫
    (GroupScheme.baseChange b).map t) =
    SubgroupFunctor.descentTransport b a ha G (Dynamic.unipotent χ)
  rw [← transportCocharacter_naturality, Dynamic.unipotent_eq_comap_of_iso _ e.symm, Iso.symm_hom]
  have h : transportCocharacter b a ha G χ ≫ e.inv = Dynamic.baseChangeCocharacter a χ := by
    simp only [transportCocharacter, Dynamic.baseChangeCocharacter, e, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [h, Dynamic.unipotent_baseChange]
  rfl

/-- The centralizer of the translated cocharacter is the coefficient
transport of the original centralizer. -/
theorem centralizer_galoisRepresentation
    (σ : E ≃ₐ[F] E)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T)) :
    Dynamic.centralizer (CommGroupScheme.groupHom
      (cocharacterLattice.galoisRepresentation F E T σ ν) ≫
      (GroupScheme.baseChange (algebraBaseMap F E)).map t) =
      SubgroupFunctor.galoisTransport F E G σ
        (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫
          (GroupScheme.baseChange (algebraBaseMap F E)).map t)) := by
  let b := algebraBaseMap F E
  let a := galoisBaseMap F E σ
  let ha := galoisBaseMap_over F E σ
  let χ := CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map t
  let e := descentBaseChangeIso b a ha G
  change Dynamic.centralizer (transportCocharacter b a ha T.toGrp (CommGroupScheme.groupHom ν) ≫
    (GroupScheme.baseChange b).map t) =
    SubgroupFunctor.descentTransport b a ha G (Dynamic.centralizer χ)
  rw [← transportCocharacter_naturality, Dynamic.centralizer_eq_comap_of_iso _ e.symm, Iso.symm_hom]
  have h : transportCocharacter b a ha G χ ≫ e.inv = Dynamic.baseChangeCocharacter a χ := by
    simp only [transportCocharacter, Dynamic.baseChangeCocharacter, e, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [h, Dynamic.centralizer_baseChange]
  rfl

end Galois

end Langlands.GroupScheme
