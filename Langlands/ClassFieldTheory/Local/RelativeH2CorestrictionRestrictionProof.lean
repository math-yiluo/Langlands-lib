import Langlands.ClassFieldTheory.Local.RelativeH2CorestrictionRestrictionStatement
import Langlands.Cohomology.Tate.TransferProof
import Langlands.Cohomology.Tate.PositiveRestriction

/-! # Relative corestriction after restriction -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- Restriction to `Gal(M/L)` followed by subgroup reindexing is ordinary
restriction to the actual subgroup `relativeGaloisSubgroup K L M`. -/
theorem relativeRestriction_comp_subgroupCohomologyIso (n : ℕ) :
    relativeRestriction K L M n ≫ (relativeSubgroupCohomologyIso K L M n).hom =
      groupCohomology.map (relativeGaloisSubgroup K L M).subtype
        (𝟙 (Rep.res (relativeGaloisSubgroup K L M).subtype (unitsRepresentation K M))) n := by
  rw [relativeSubgroupCohomologyIso, groupCohomology.mapIso_hom, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro σ
    change ((relativeGaloisSubgroupEquiv K L M).symm σ).restrictScalars K = (σ : Gal(M/K))
    rw [← relativeGaloisSubgroupEquiv_apply, MulEquiv.apply_symm_apply]
  · rfl

/-- In every positive degree, relative corestriction after relative restriction
is multiplication by the index of the actual subgroup. -/
theorem relativeCorestriction_relativeRestriction [FiniteDimensional K M]
    (n : ℕ) [NeZero n] (x : relativeCohomology K M n) :
    relativeCorestriction K L M n (relativeRestriction K L M n x) =
      (relativeGaloisSubgroup K L M).index • x := by
  let _ := Fintype.ofFinite Gal(M/K)
  let _ := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let _ := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  let H := relativeGaloisSubgroup K L M
  let A := unitsRepresentation K M
  let eA := (TateCohomology.isoGroupCohomology n).app A
  let eB := (TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype A)
  have key : Langlands.Tate.restriction H A n (eA.inv x) =
      eB.inv ((relativeSubgroupCohomologyIso K L M n).hom (relativeRestriction K L M n x)) := by
    have h1 := ConcreteCategory.congr_hom (Langlands.Tate.restriction_groupCohomology H A n)
      (eA.inv x)
    have h2 := ConcreteCategory.congr_hom (relativeRestriction_comp_subgroupCohomologyIso K L M n)
      x
    simp only [ModuleCat.hom_ofHom, ConcreteCategory.comp_apply] at h1 h2
    rw [h1, h2]
    exact congrArg (fun y => eB.inv (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n y))
      (Iso.inv_hom_id_apply eA x)
  change eA.hom (Langlands.Tate.corestriction H A n
      (eB.inv ((relativeSubgroupCohomologyIso K L M n).hom (relativeRestriction K L M n x)))) =
    H.index • x
  rw [← key, Langlands.Tate.corestriction_restriction, map_nsmul, Iso.inv_hom_id_apply]

/-- For finite Galois `M/K` and `M/L`, the actual subgroup fixing `L` has
index `[L : K]`. -/
theorem relativeGaloisSubgroup_index [FiniteDimensional K L] [FiniteDimensional K M]
    [FiniteDimensional L M] [IsGalois K M] [IsGalois L M] :
    (relativeGaloisSubgroup K L M).index = Module.finrank K L := by
  have h := (relativeGaloisSubgroup K L M).index_mul_card
  rw [← Nat.card_congr (relativeGaloisSubgroupEquiv K L M).toEquiv,
    IsGalois.card_aut_eq_finrank L M, IsGalois.card_aut_eq_finrank K M,
    ← Module.finrank_mul_finrank K L M] at h
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h

end Tower

/-- Degree-two relative corestriction after restriction is multiplication by
the degree of the middle field. -/
theorem relativeH2CorestrictionRestriction :
    RelativeH2CorestrictionRestrictionStatement.{u} := by
  intro K L M _ _ _ _ _ _ _ _ _ _ _ _ x
  rw [relativeCorestriction_relativeRestriction, relativeGaloisSubgroup_index]

end Langlands.ClassFieldTheory.Local
