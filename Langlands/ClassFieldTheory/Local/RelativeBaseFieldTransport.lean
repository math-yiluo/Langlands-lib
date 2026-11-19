import Langlands.ClassFieldTheory.Local.Corestriction
import Langlands.Cohomology.Continuous.CorestrictionInflation
import Langlands.Cohomology.Tate.PositiveCorestriction
import Langlands.Galois.Local.AbsoluteDefinitions

/-! # Relative unit cohomology under replacement of the upper base -/

noncomputable section

open CategoryTheory Langlands.Continuous Langlands.LocalGalois

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

variable {K L E M : Type u} [Field K] [Field L] [Field E] [Field M]
  [Algebra K L] [Algebra K E] [Algebra K M] [Algebra L M] [Algebra E M]
  [IsScalarTower K L M] [IsScalarTower K E M]
  (b : L ≃ₐ[K] E) (hb : ∀ x, algebraMap L M x = algebraMap E M (b x))

omit [IsScalarTower K L M] [IsScalarTower K E M] in
/-- A change of upper base that preserves its embedding acts trivially on
the underlying automorphisms of the common finite Galois field. -/
def relativeBaseFieldAutEquiv : Gal(M/L) ≃* Gal(M/E) :=
  semilinearAutCongr b.toRingEquiv (RingEquiv.refl M) hb

omit [IsScalarTower K L M] [IsScalarTower K E M] in
/-- Reindex ordinary relative cohomology by the base isomorphism with the
identity map of units of the unchanged top field. -/
def relativeBaseFieldCohomologyIso (q : ℕ) :
    relativeCohomology L M q ≅ relativeCohomology E M q :=
  groupCohomology.mapIso (relativeBaseFieldAutEquiv b hb)
    (LinearEquiv.refl IntegerScalars.{u} (Additive Mˣ)) (fun _ => rfl) q

local notation "JL" => relativeGaloisSubgroup K L M
local notation "JE" => relativeGaloisSubgroup K E M
local notation "V" => unitsRepresentation K M

private def relativeBaseImageEquiv : JL ≃* JE :=
  (relativeGaloisSubgroupEquiv K L M).symm.trans
    ((relativeBaseFieldAutEquiv b hb).trans (relativeGaloisSubgroupEquiv K E M))

private theorem relativeBaseImageEquiv_val (g : JL) :
    (relativeBaseImageEquiv b hb g : Gal(M/K)) = g.val := by
  let e := relativeGaloisSubgroupEquiv K L M
  change (e (e.symm g) : Gal(M/K)) = g.val
  rw [e.apply_symm_apply]

private theorem relativeBaseImageEquiv_symm_val (g : JE) :
    ((relativeBaseImageEquiv b hb).symm g : Gal(M/K)) = g.val :=
  (relativeBaseImageEquiv_val b hb ((relativeBaseImageEquiv b hb).symm g)).symm.trans
    (congrArg Subtype.val ((relativeBaseImageEquiv b hb).apply_symm_apply g))

private def relativeBaseImageCohomologyIso (q : ℕ) :
    groupCohomology (Rep.res (JL).subtype V) q ≅
      groupCohomology (Rep.res (JE).subtype V) q :=
  groupCohomology.mapIso (relativeBaseImageEquiv b hb)
    (LinearEquiv.refl IntegerScalars.{u} (Additive Mˣ)) intertwines q
where
  intertwines g := by
    change (V).ρ g.val = (V).ρ (relativeBaseImageEquiv b hb g).val
    rw [relativeBaseImageEquiv_val]

private theorem relativeBaseImageCohomologyIso_comp (q : ℕ) :
    (relativeSubgroupCohomologyIso K L M q).hom ≫
        (relativeBaseImageCohomologyIso b hb q).hom =
      (relativeBaseFieldCohomologyIso b hb q).hom ≫
        (relativeSubgroupCohomologyIso K E M q).hom := by
  unfold relativeSubgroupCohomologyIso relativeBaseImageCohomologyIso
    relativeBaseFieldCohomologyIso
  simp only [groupCohomology.mapIso_hom, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro g
    let e := relativeGaloisSubgroupEquiv K L M
    change e.symm (e ((relativeBaseFieldAutEquiv b hb).symm
      ((relativeGaloisSubgroupEquiv K E M).symm g))) = _
    exact e.symm_apply_apply _
  · rfl

private theorem relativeCorestriction_ordinaryForm
    (K' L' M' : Type u) [Field K'] [Field L'] [Field M'] [Algebra K' L'] [Algebra K' M']
    [Algebra L' M'] [IsScalarTower K' L' M'] [FiniteDimensional K' M'] (q : ℕ) [NeZero q] :
    let J := relativeGaloisSubgroup K' L' M'
    letI : Fintype (Gal(M'/K') ⧸ J) := Fintype.ofFinite _
    ModuleCat.ofHom (relativeCorestriction K' L' M' q) =
      (relativeSubgroupCohomologyIso K' L' M' q).hom ≫
        Langlands.Tate.ordinaryCohomologyCorestriction J (unitsRepresentation K' M') q := by
  let J := relativeGaloisSubgroup K' L' M'
  let : Fintype Gal(M'/K') := Fintype.ofFinite _
  let : Fintype J := Fintype.ofFinite _
  let : Fintype (Gal(M'/K') ⧸ J) := Fintype.ofFinite _
  let A := unitsRepresentation K' M'
  let e := (TateCohomology.isoGroupCohomology q).app A
  let e' := (TateCohomology.isoGroupCohomology q).app (Rep.res J.subtype A)
  change (relativeSubgroupCohomologyIso K' L' M' q).hom ≫ e'.inv ≫
    ModuleCat.ofHom (Langlands.Tate.corestriction J A q) ≫ e.hom = _
  rw [Langlands.Tate.corestriction_groupCohomology]
  change _ ≫ e'.inv ≫ (e'.hom ≫ Langlands.Tate.ordinaryCohomologyCorestriction J A q ≫
    e.inv) ≫ e.hom = _
  simp only [Category.assoc, e'.inv_hom_id_assoc, e.inv_hom_id]
  exact congrArg (fun f => (relativeSubgroupCohomologyIso K' L' M' q).hom ≫ f)
    (Category.comp_id (Langlands.Tate.ordinaryCohomologyCorestriction J A q))

variable [FiniteDimensional K M]

local instance relativeBaseLCosetFintype : Fintype (Gal(M/K) ⧸ JL) := Fintype.ofFinite _
local instance relativeBaseECosetFintype : Fintype (Gal(M/K) ⧸ JE) := Fintype.ofFinite _

private theorem relativeBaseImageCorestriction (q : ℕ) :
    Langlands.Tate.ordinaryCohomologyCorestriction JL V q =
      (relativeBaseImageCohomologyIso b hb q).hom ≫
        Langlands.Tate.ordinaryCohomologyCorestriction JE V q := by
  have hm (g : Gal(M/K)) : g ∈ JE ↔ g ∈ JL := by
    constructor
    · intro hg
      let x := (relativeBaseImageEquiv b hb).symm (⟨g, hg⟩ : JE)
      have hx : x.val = g := relativeBaseImageEquiv_symm_val b hb ⟨g, hg⟩
      exact hx ▸ x.property
    · intro hg
      let x := relativeBaseImageEquiv b hb (⟨g, hg⟩ : JL)
      have hx : x.val = g := relativeBaseImageEquiv_val b hb ⟨g, hg⟩
      exact hx ▸ x.property
  unfold relativeBaseImageCohomologyIso
  rw [groupCohomology.mapIso_hom]
  let f : Rep.res (relativeBaseImageEquiv b hb).symm.toMonoidHom
      (Rep.res (JL).subtype V) ⟶ Rep.res (JE).subtype V :=
    Rep.ofHom ⟨LinearMap.id, fun g => by
      change (V).ρ ((relativeBaseImageEquiv b hb).symm g).val = (V).ρ g.val
      rw [relativeBaseImageEquiv_symm_val]⟩
  have h := ordinaryCohomologyCorestriction_comp_map (MonoidHom.id Gal(M/K))
    Function.surjective_id JL JE hm (relativeBaseImageEquiv b hb).symm.toMonoidHom
    (relativeBaseImageEquiv_symm_val b hb) V V (𝟙 (V)) f rfl q
  rw [groupCohomology.map_id, Category.comp_id] at h
  exact h

/-- Relative corestriction is preserved by the actual base reindexing. -/
theorem relativeBaseFieldCohomologyIso_corestriction (q : ℕ) [NeZero q] :
    (relativeBaseFieldCohomologyIso b hb q).hom ≫
        ModuleCat.ofHom (relativeCorestriction K E M q) =
      ModuleCat.ofHom (relativeCorestriction K L M q) := by
  rw [relativeCorestriction_ordinaryForm K E M, relativeCorestriction_ordinaryForm K L M,
    ← Category.assoc, ← relativeBaseImageCohomologyIso_comp b hb, Category.assoc,
    ← relativeBaseImageCorestriction b hb]

end Langlands.ClassFieldTheory.Local
