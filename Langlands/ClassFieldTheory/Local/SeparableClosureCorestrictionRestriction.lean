import Langlands.Algebra.BrauerComparison.Naturality
import Langlands.ClassFieldTheory.Local.SeparableClosureCorestrictionComparison

/-! # The restriction paired with absolute separable-unit corestriction -/

noncomputable section

open CategoryTheory Langlands.Continuous Langlands.BrauerComparison

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

local notation "S" => SeparableClosure K
local notation "T" => SeparableClosure L
local notation "E" => separableClosureBase K L

private abbrev restrictionClosureAlgebra : Algebra S T :=
  (separableClosureTowerEquiv K L).toRingEquiv.toRingHom.toAlgebra

omit [FiniteDimensional K L] in
private theorem restrictionClosureTower :
    letI := restrictionClosureAlgebra K L
    IsScalarTower K S T :=
  IsScalarTower.of_algHom (separableClosureTowerEquiv K L).toAlgHom

omit [FiniteDimensional K L] in
private theorem separableUnitRestrictionBySubgroup_eq_continuousUnitRestriction (q : ℕ) :
    letI := restrictionClosureAlgebra K L
    letI := restrictionClosureTower K L
    separableUnitRestrictionBySubgroup K L q = continuousUnitRestriction K L S T q := by
  let := restrictionClosureAlgebra K L
  let := restrictionClosureTower K L
  unfold separableUnitRestrictionBySubgroup intermediateUnitRestriction intermediateUnitCohomologyIso
    separableClosureUpperUnitIso unitCohomologyIsoOfRingEquiv continuousRestriction
    continuousUnitRestriction
  rw [continuousCohomologyIso_hom, continuousCohomologyIso_hom, Category.assoc,
    ← ContinuousCohomology.map_comp, ← ContinuousCohomology.map_comp]
  apply congrArg (fun f => HomologicalComplex.homologyMap f q)
  apply continuousCochainsMap_congr
  · apply ContinuousMonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    let b := (separableClosureBaseEquiv K L).symm.toRingEquiv
    let e := (separableClosureTowerEquiv K L).toRingEquiv
    let he := separableClosureTowerEquiv_base K L
    apply e.injective
    change e ((krullAutContinuousEquiv b e he).symm σ x) =
      e (((σ.restrictScalars K).restrictNormal S) x)
    exact (krullAutContinuousEquiv_symm_apply b e he σ x).trans
      (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) S x).symm
  · intro x
    apply Units.ext
    rfl

omit [FiniteDimensional K L] in
/-- The open-subgroup restriction agrees in degree two with the canonical
separable-closure restriction used by the actual Brauer comparison. -/
theorem separableUnitRestrictionBySubgroup_eq (x : separableH2 K) :
    separableUnitRestrictionBySubgroup K L 2 x = separableRestriction K L x := by
  let := restrictionClosureAlgebra K L
  let := restrictionClosureTower K L
  have h := ConcreteCategory.congr_hom
    (separableUnitRestrictionBySubgroup_eq_continuousUnitRestriction K L 2) x
  obtain ⟨a, rfl⟩ := (brauerEquiv K).surjective x
  rw [← brauerEquiv_scalarExtension]
  exact h.trans (brauerContinuousEquiv_scalarExtension K L S T a).symm

/-- Absolute corestriction after the canonical separable-cohomology
restriction is multiplication by the actual field degree. -/
theorem separableUnitCorestriction_separableRestriction (x : separableH2 K) :
    separableUnitCorestriction K L 2 (separableRestriction K L x) =
      Module.finrank K L • x := by
  have h := ConcreteCategory.congr_hom
    (separableUnitRestrictionBySubgroup_corestriction K L 2) x
  change separableUnitCorestriction K L 2 (separableUnitRestrictionBySubgroup K L 2 x) =
    Module.finrank K L • x at h
  rw [separableUnitRestrictionBySubgroup_eq] at h
  exact h

/-- The continuous unit corestriction in the additive groups used by the
actual Brauer comparison. -/
def separableH2Corestriction : separableH2 L →+ separableH2 K :=
  (separableUnitCorestriction K L 2).hom.toAddMonoidHom

theorem separableH2Corestriction_separableRestriction (x : separableH2 K) :
    separableH2Corestriction K L (separableRestriction K L x) = Module.finrank K L • x :=
  separableUnitCorestriction_separableRestriction K L x

end Langlands.ClassFieldTheory.Local
