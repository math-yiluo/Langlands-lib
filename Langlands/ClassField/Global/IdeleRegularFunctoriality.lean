import Langlands.ClassField.Global.IdeleRegularClasses

/-! # Regular idele-class cohomology under inflation and restriction -/

noncomputable section

namespace Langlands.ClassField.Global

open CategoryTheory

universe u

section Inflation

variable (F E K : Type u) [Field F] [Field E] [Field K]
  [NumberField F] [NumberField E] [NumberField K]
  [Algebra F E] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
  [IsGalois F E] [IsGalois F K]

/-- A class is regular if and only if its inflation to a finite Galois extension is
regular. The reverse direction only uses transitivity; the forward direction uses
a common overfield of the regularity witness and the prescribed extension. -/
theorem isRegularIdeleClass_inflation_iff (c : relativeIdeleClassCohomology F E 2) :
    IsRegularIdeleClass F K (relativeIdeleClassInflation F E K 2 c) ↔
      IsRegularIdeleClass F E c := by
  constructor
  · rintro ⟨L, _, _, _, _, _, _, hc⟩
    let : Algebra E L := ((algebraMap K L).comp (algebraMap E K)).toAlgebra
    let : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap F L x = algebraMap K L (algebraMap E K (algebraMap F E x))
      rw [← IsScalarTower.algebraMap_apply F E K, ← IsScalarTower.algebraMap_apply F K L]
    apply isRegularIdeleClass_of_mem F E (L := L)
    change relativeIdeleClassInflation F E L 2 c ∈
      (ideleQuotientCohomologyMap F L 2).hom.toAddMonoidHom.range
    rw [← ideleClassInflationTransitivity F E K L 2 c]
    exact hc
  · intro hc
    rcases hc with ⟨L, _, _, _, _, _, _, hc⟩
    let M := commonGaloisOverfield F E L K
    apply isRegularIdeleClass_of_mem F K (L := M.carrier)
    change relativeIdeleClassInflation F K M.carrier 2
      (relativeIdeleClassInflation F E K 2 c) ∈
      (ideleQuotientCohomologyMap F M.carrier 2).hom.toAddMonoidHom.range
    rw [ideleClassInflationTransitivity F E K M.carrier 2 c]
    exact ideleClassRegularSubgroup_le F E L M.carrier hc

/-- Inflation on regular classes, obtained by restricting actual idele-class inflation. -/
def regularIdeleClassInflation :
    regularIdeleClassSubgroup F E →+ regularIdeleClassSubgroup F K where
  toFun c := ⟨relativeIdeleClassInflation F E K 2 c,
    (isRegularIdeleClass_inflation_iff F E K c).2 c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext ((relativeIdeleClassInflation F E K 2).hom.map_add c.val d.val)

@[simp]
theorem regularIdeleClassInflation_coe (c : regularIdeleClassSubgroup F E) :
    (regularIdeleClassInflation F E K c : relativeIdeleClassCohomology F K 2) =
      relativeIdeleClassInflation F E K 2 c := rfl

end Inflation

section Restriction

variable (F K E : Type u) [Field F] [Field K] [Field E]
  [NumberField F] [NumberField K] [NumberField E]
  [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
  [IsGalois F E]

/-- Restriction of a regular class is regular, including for a nonnormal intermediate
base field. The same extension witnesses regularity after restriction. -/
theorem isRegularIdeleClass_restriction {c : relativeIdeleClassCohomology F E 2}
    (hc : IsRegularIdeleClass F E c) :
    let := IsGalois.tower_top_of_isGalois F K E
    IsRegularIdeleClass K E (relativeIdeleClassRestriction F K E 2 c) := by
  let := IsGalois.tower_top_of_isGalois F K E
  rcases hc with ⟨L, _, _, _, _, _, _, hc⟩
  let : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap F L x = algebraMap E L (algebraMap K E (algebraMap F K x))
    rw [← IsScalarTower.algebraMap_apply F K E, ← IsScalarTower.algebraMap_apply F E L]
  let := IsGalois.tower_top_of_isGalois F K L
  apply isRegularIdeleClass_of_mem K E (L := L)
  rcases hc with ⟨a, ha⟩
  refine ⟨relativeIdeleRestriction F K L 2 a, ?_⟩
  calc
    ideleQuotientCohomologyMap K L 2 (relativeIdeleRestriction F K L 2 a) =
        relativeIdeleClassRestriction F K L 2 (ideleQuotientCohomologyMap F L 2 a) :=
      ConcreteCategory.congr_hom (relativeIdeleRestriction_comp_quotient F K L 2) a
    _ = relativeIdeleClassRestriction F K L 2 (relativeIdeleClassInflation F E L 2 c) :=
      congrArg _ ha
    _ = relativeIdeleClassInflation K E L 2 (relativeIdeleClassRestriction F K E 2 c) :=
      ideleClassInflationRestrictionCompatibility F K E L 2 c

/-- Restriction on regular classes, obtained by restricting actual idele-class restriction. -/
def regularIdeleClassRestriction :
    let := IsGalois.tower_top_of_isGalois F K E
    regularIdeleClassSubgroup F E →+ regularIdeleClassSubgroup K E := by
  let := IsGalois.tower_top_of_isGalois F K E
  exact
    { toFun := fun c => ⟨relativeIdeleClassRestriction F K E 2 c,
        isRegularIdeleClass_restriction F K E c.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun c d => Subtype.ext
        ((relativeIdeleClassRestriction F K E 2).hom.map_add c.val d.val) }

@[simp]
theorem regularIdeleClassRestriction_coe (c : regularIdeleClassSubgroup F E) :
    let := IsGalois.tower_top_of_isGalois F K E
    (regularIdeleClassRestriction F K E c : relativeIdeleClassCohomology K E 2) =
      relativeIdeleClassRestriction F K E 2 c := rfl

end Restriction

end Langlands.ClassField.Global
