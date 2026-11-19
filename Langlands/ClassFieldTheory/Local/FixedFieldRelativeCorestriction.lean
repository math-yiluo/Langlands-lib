import Langlands.ClassFieldTheory.Local.Corestriction
import Langlands.ClassFieldTheory.Local.IntermediateUnitCorestriction
import Langlands.ClassFieldTheory.Local.SeparableUnramifiedInflation
import Langlands.Cohomology.Tate.PositiveCorestriction

/-! # Relative unit corestriction at finite Galois quotient stages -/

noncomputable section

open CategoryTheory Langlands.Continuous

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : IntermediateField K Ω) (N : OpenNormalSubgroup Gal(Ω/K))

private abbrev transferFixedField : Type u :=
  ↥(IntermediateField.fixedField N.toSubgroup)

local notation "NC" => FixedFieldRefinement.closed K Ω N
local notation "M" => transferFixedField K Ω N
local notation "Q" => Gal(Ω/K) ⧸ N.toSubgroup
local notation "H" => E.fixingSubgroup
local notation "I" => Subgroup.map (QuotientGroup.mk' N.toSubgroup) H
local notation "J" => relativeGaloisSubgroup K E M
set_option quotPrecheck false in
local notation "fixedAction" => (unitsRepresentation K Ω).quotientToInvariants N.toSubgroup
local notation "relativeAction" => unitsRepresentation K M

variable [Algebra E (IntermediateField.fixedField N.toSubgroup)]
    [IsScalarTower K E (IntermediateField.fixedField N.toSubgroup)]
    [IsScalarTower E (IntermediateField.fixedField N.toSubgroup) Ω]

/-- The image of the fixing group in the finite quotient identifies with
the actual subgroup of fixed-field automorphisms over the upper base. -/
def fixedFieldQuotientImageEquiv : I ≃* J :=
  (quotientSubgroupEquiv H N.toSubgroup).symm.trans
    ((fixedFieldRestrictedGroupEquiv K Ω E NC).trans
      (relativeGaloisSubgroupEquiv K E M))

private theorem fixedFieldQuotientImageEquiv_apply (g : I) :
    (fixedFieldQuotientImageEquiv K Ω E N g : Gal(M/K)) =
      InfiniteGalois.normalAutEquivQuotient (NC) g.1 := by
  let e := quotientSubgroupEquiv H N.toSubgroup
  have h := DFunLike.congr_fun (fixedFieldRestrictedGroupEquiv_commutes K Ω E (NC))
    (e.symm g)
  change InfiniteGalois.normalAutEquivQuotient (NC) (e (e.symm g)).1 =
    (fixedFieldQuotientImageEquiv K Ω E N g : Gal(M/K)) at h
  rw [e.apply_symm_apply] at h
  exact h.symm

private theorem fixedFieldQuotient_mem_iff (g : Q) :
    g ∈ I ↔ InfiniteGalois.normalAutEquivQuotient (NC) g ∈ J := by
  constructor
  · intro hg
    rw [← fixedFieldQuotientImageEquiv_apply K Ω E N ⟨g, hg⟩]
    exact (fixedFieldQuotientImageEquiv K Ω E N ⟨g, hg⟩).2
  · intro hg
    let e := fixedFieldQuotientImageEquiv K Ω E N
    let y := e.symm ⟨InfiniteGalois.normalAutEquivQuotient (NC) g, hg⟩
    have he := congrArg Subtype.val (e.apply_symm_apply
      (⟨InfiniteGalois.normalAutEquivQuotient (NC) g, hg⟩ : J))
    change (e y : Gal(M/K)) = InfiniteGalois.normalAutEquivQuotient (NC) g at he
    have hy := (InfiniteGalois.normalAutEquivQuotient (NC)).injective
      ((fixedFieldQuotientImageEquiv_apply K Ω E N y).symm.trans he)
    exact hy ▸ y.2

private theorem fixedFieldQuotientImageUnits_intertwines (g : I) :
    (fixedFieldUnitsLinearEquiv K Ω N.toSubgroup).toLinearMap ∘ₗ
        (Rep.res (I).subtype fixedAction).ρ g =
      (Rep.res (J).subtype relativeAction).ρ (fixedFieldQuotientImageEquiv K Ω E N g) ∘ₗ
        (fixedFieldUnitsLinearEquiv K Ω N.toSubgroup).toLinearMap := by
  change _ = (unitsRepresentation K M).ρ
    (fixedFieldQuotientImageEquiv K Ω E N g : Gal(M/K)) ∘ₗ _
  rw [fixedFieldQuotientImageEquiv_apply]
  exact fixedFieldUnitsLinearEquiv_intertwines K Ω (NC) g.1

private def fixedFieldQuotientImageCohomologyIso (q : ℕ) :
    groupCohomology (Rep.res (I).subtype fixedAction) q ≅
      groupCohomology (Rep.res (J).subtype relativeAction) q :=
  groupCohomology.mapIso (fixedFieldQuotientImageEquiv K Ω E N)
    (fixedFieldUnitsLinearEquiv K Ω N.toSubgroup)
    (fixedFieldQuotientImageUnits_intertwines K Ω E N) q

set_option maxHeartbeats 600000 in
private theorem fixedFieldQuotientImageCohomologyIso_comp
    (hNE : N.toSubgroup ≤ H) (q : ℕ) :
    (quotientSubgroupCohomologyIso (unitsRepresentation K Ω) H N.toSubgroup hNE q).hom ≫
        (fixedFieldQuotientImageCohomologyIso K Ω E N q).hom =
      (fixedFieldRestrictedCohomologyIso K Ω E (NC) hNE q).hom ≫
        (relativeSubgroupCohomologyIso K E M q).hom := by
  unfold quotientSubgroupCohomologyIso fixedFieldQuotientImageCohomologyIso
    fixedFieldRestrictedCohomologyIso relativeSubgroupCohomologyIso
  rw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
    groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro x
    let e := quotientSubgroupEquiv H N.toSubgroup
    change e.symm (e ((fixedFieldRestrictedGroupEquiv K Ω E (NC)).symm
      ((relativeGaloisSubgroupEquiv K E M).symm x))) = _
    exact e.symm_apply_apply _
  · apply LinearMap.ext
    intro x
    apply Units.ext
    apply Subtype.ext
    rfl

local instance transferFixedFieldFiniteDimensional : FiniteDimensional K M :=
  fixedField_openNormal_finiteDimensional K Ω N
local instance transferAmbientQuotientFinite : Finite Q := finite_quotient N
local instance transferImageCosetsFintype : Fintype (Q ⧸ I) := Fintype.ofFinite _
local instance transferRelativeCosetsFintype : Fintype (Gal(M/K) ⧸ J) := by
  let : Finite Gal(M/K) := inferInstance
  exact Fintype.ofFinite (Gal(M/K) ⧸ J)

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryCorestriction_fixedFieldQuotientImage_inv (q : ℕ) :
    Langlands.Tate.ordinaryCohomologyCorestriction J relativeAction q ≫
        (fixedFieldCohomologyIso K Ω (NC) q).inv =
      (fixedFieldQuotientImageCohomologyIso K Ω E N q).inv ≫
        Langlands.Tate.ordinaryCohomologyCorestriction I fixedAction q := by
  unfold fixedFieldQuotientImageCohomologyIso fixedFieldCohomologyIso
  rw [groupCohomology.mapIso_inv, groupCohomology.mapIso_inv]
  exact ordinaryCohomologyCorestriction_comp_map
    (InfiniteGalois.normalAutEquivQuotient (NC)).toMonoidHom
    (InfiniteGalois.normalAutEquivQuotient (NC)).surjective
    J I (fixedFieldQuotient_mem_iff K Ω E N)
    (fixedFieldQuotientImageEquiv K Ω E N).toMonoidHom
    (fixedFieldQuotientImageEquiv_apply K Ω E N)
    relativeAction fixedAction _ _ rfl q

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryCorestriction_fixedFieldQuotientImage (q : ℕ) :
    Langlands.Tate.ordinaryCohomologyCorestriction I fixedAction q ≫
        (fixedFieldCohomologyIso K Ω (NC) q).hom =
      (fixedFieldQuotientImageCohomologyIso K Ω E N q).hom ≫
        Langlands.Tate.ordinaryCohomologyCorestriction J relativeAction q := by
  let e := fixedFieldCohomologyIso K Ω (NC) q
  let e' := fixedFieldQuotientImageCohomologyIso K Ω E N q
  apply (cancel_mono e.inv).mp
  have h := ordinaryCorestriction_fixedFieldQuotientImage_inv K Ω E N q
  change Langlands.Tate.ordinaryCohomologyCorestriction J relativeAction q ≫ e.inv =
    e'.inv ≫ Langlands.Tate.ordinaryCohomologyCorestriction I fixedAction q at h
  change (_ ≫ e.hom) ≫ e.inv = (e'.hom ≫ _) ≫ e.inv
  simp only [Category.assoc, e.hom_inv_id, Category.comp_id, h, e'.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem relativeCorestriction_eq_ordinary (q : ℕ) [NeZero q] :
    ModuleCat.ofHom (relativeCorestriction K E M q) =
      (relativeSubgroupCohomologyIso K E M q).hom ≫
        Langlands.Tate.ordinaryCohomologyCorestriction J relativeAction q := by
  let : Fintype Gal(M/K) := Fintype.ofFinite _
  let : Fintype J := Fintype.ofFinite _
  let e := (TateCohomology.isoGroupCohomology q).app relativeAction
  let e' := (TateCohomology.isoGroupCohomology q).app (Rep.res (J).subtype relativeAction)
  change (relativeSubgroupCohomologyIso K E M q).hom ≫ e'.inv ≫
    ModuleCat.ofHom (Langlands.Tate.corestriction J relativeAction q) ≫ e.hom = _
  rw [Langlands.Tate.corestriction_groupCohomology]
  change _ ≫ e'.inv ≫ (e'.hom ≫ Langlands.Tate.ordinaryCohomologyCorestriction J
    relativeAction q ≫ e.inv) ≫ e.hom = _
  simp only [Category.assoc, e'.inv_hom_id_assoc, e.inv_hom_id]
  exact congrArg (fun f => (relativeSubgroupCohomologyIso K E M q).hom ≫ f)
    (Category.comp_id (Langlands.Tate.ordinaryCohomologyCorestriction J relativeAction q))

/-- Under the fixed-field comparisons, the actual finite quotient
transfer is the relative corestriction of the finite field extension. -/
theorem finiteCorestriction_fixedFieldCohomologyIso [FiniteDimensional K E]
    (hNE : N.toSubgroup ≤ H) (q : ℕ) [NeZero q] :
    finiteCorestriction (galoisUnitDiscreteModule K Ω).toRep
        (intermediateFieldFixingOpenSubgroup K Ω E) N hNE q ≫
        (fixedFieldCohomologyIso K Ω (NC) q).hom =
      (fixedFieldRestrictedCohomologyIso K Ω E (NC) hNE q).hom ≫
        ModuleCat.ofHom (relativeCorestriction K E M q) := by
  unfold finiteCorestriction quotientCorestriction
  change (quotientSubgroupCohomologyIso (unitsRepresentation K Ω) H N.toSubgroup hNE q).hom ≫
      Langlands.Tate.ordinaryCohomologyCorestriction I fixedAction q ≫
        (fixedFieldCohomologyIso K Ω (NC) q).hom = _
  rw [ordinaryCorestriction_fixedFieldQuotientImage K Ω E N q,
    ← Category.assoc, fixedFieldQuotientImageCohomologyIso_comp K Ω E N hNE q,
    Category.assoc, relativeCorestriction_eq_ordinary K Ω E N q]

end Langlands.ClassFieldTheory.Local
