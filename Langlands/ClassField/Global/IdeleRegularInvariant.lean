import Langlands.ClassField.Global.IdeleRegularFunctoriality

/-! # Invariants on regular classes from compatible idele invariants -/

noncomputable section

namespace Langlands.ClassField.Global

open CategoryTheory Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

/-- Additive maps on the actual idele `H²` for all Galois number-field extensions.
No compatibility is built into this type. -/
abbrev IdeleInvariantMaps : Type (u + 1) :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E],
    relativeIdeleCohomology F E 2 →+ RationalModIntegers

namespace IdeleInvariantMaps

/-- The maps vanish on the kernel of the actual idele-class quotient map. -/
def KillsQuotientKernel (s : IdeleInvariantMaps.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] (a : relativeIdeleCohomology F E 2),
    ideleQuotientCohomologyMap F E 2 a = 0 → s F E a = 0

/-- Actual idele inflation preserves the maps. -/
def InflationCompatible (s : IdeleInvariantMaps.{u}) : Prop :=
  ∀ (F E L : Type u) [Field F] [Field E] [Field L]
    [NumberField F] [NumberField E] [NumberField L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [IsGalois F E] [IsGalois F L] (a : relativeIdeleCohomology F E 2),
    s F L (relativeIdeleInflation F E L 2 a) = s F E a

/-- Actual idele restriction multiplies the maps by the base-extension degree. -/
def RestrictionCompatible (s : IdeleInvariantMaps.{u}) : Prop :=
  ∀ (F K E : Type u) [Field F] [Field K] [Field E]
    [NumberField F] [NumberField K] [NumberField E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [IsGalois F E],
    let := IsGalois.tower_top_of_isGalois F K E
    ∀ a : relativeIdeleCohomology F E 2,
      s K E (relativeIdeleRestriction F K E 2 a) = Module.finrank F K • s F E a

end IdeleInvariantMaps

variable (s : IdeleInvariantMaps.{u}) (hker : s.KillsQuotientKernel)
  (hInf : s.InflationCompatible)

section Construction

variable (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]

private theorem value_exists (c : regularIdeleClassSubgroup F E) :
    ∃ y : RationalModIntegers,
      ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
        (_ : Algebra E L) (_ : IsScalarTower F E L) (_ : IsGalois F L)
        (a : relativeIdeleCohomology F L 2),
        ideleQuotientCohomologyMap F L 2 a = relativeIdeleClassInflation F E L 2 c.val ∧
          s F L a = y := by
  rcases c.property with ⟨L, _, _, _, _, _, _, a, ha⟩
  exact ⟨s F L a, L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, a, ha, rfl⟩

private def regularValue (c : regularIdeleClassSubgroup F E) : RationalModIntegers :=
  Classical.choose (value_exists s F E c)

include hker hInf in
private theorem regularValue_eq
    {L : Type u} [Field L] [NumberField L] [Algebra F L] [Algebra E L]
    [IsScalarTower F E L] [IsGalois F L]
    (c : regularIdeleClassSubgroup F E) (a : relativeIdeleCohomology F L 2)
    (ha : ideleQuotientCohomologyMap F L 2 a =
      relativeIdeleClassInflation F E L 2 c.val) :
    regularValue s F E c = s F L a := by
  rcases Classical.choose_spec (value_exists s F E c) with
    ⟨K, _, _, _, _, _, _, b, hb, hs⟩
  let M := commonGaloisOverfield F E L K
  have hab : ideleQuotientCohomologyMap F M.carrier 2
      (relativeIdeleInflation F L M.carrier 2 a) =
      ideleQuotientCohomologyMap F M.carrier 2
        (relativeIdeleInflation F K M.carrier 2 b) := by
    calc
      _ = relativeIdeleClassInflation F L M.carrier 2
          (ideleQuotientCohomologyMap F L 2 a) :=
        ConcreteCategory.congr_hom (relativeIdeleInflation_comp_quotient F L M.carrier 2) a
      _ = relativeIdeleClassInflation F E M.carrier 2 c.val := by
        rw [ha, ideleClassInflationTransitivity]
      _ = relativeIdeleClassInflation F K M.carrier 2
          (ideleQuotientCohomologyMap F K 2 b) := by
        rw [hb, ideleClassInflationTransitivity]
      _ = _ :=
        (ConcreteCategory.congr_hom (relativeIdeleInflation_comp_quotient F K M.carrier 2) b).symm
  have hz := hker F M.carrier
    (relativeIdeleInflation F L M.carrier 2 a -
      relativeIdeleInflation F K M.carrier 2 b)
    (by rw [map_sub, hab, sub_self])
  rw [map_sub, sub_eq_zero, hInf F L M.carrier, hInf F K M.carrier] at hz
  exact hs.symm.trans hz.symm

/-- The invariant on actual regular classes, defined using any idele representative
after finite Galois inflation. -/
def regularIdeleClassInvariant : regularIdeleClassSubgroup F E →+ RationalModIntegers where
  toFun := regularValue s F E
  map_zero' := by
    rw [regularValue_eq s hker hInf F E (L := E) 0 0 (by simp), map_zero]
  map_add' c d := by
    rcases isRegularIdeleClass_common_extension F E c.property d.property with
      ⟨M, _, _, _, _, _, _, hc, hd⟩
    rcases hc with ⟨a, ha⟩
    rcases hd with ⟨b, hb⟩
    change ideleQuotientCohomologyMap F M 2 a =
      relativeIdeleClassInflation F E M 2 c.val at ha
    change ideleQuotientCohomologyMap F M 2 b =
      relativeIdeleClassInflation F E M 2 d.val at hb
    have hab : ideleQuotientCohomologyMap F M 2 (a + b) =
        relativeIdeleClassInflation F E M 2 (c + d).val := by
      rw [map_add, ha, hb]
      exact (map_add _ c.val d.val).symm
    rw [regularValue_eq s hker hInf F E (c + d) (a + b) hab,
      regularValue_eq s hker hInf F E c a ha,
      regularValue_eq s hker hInf F E d b hb, map_add]

/-- Every representative in every witnessing extension computes the same invariant. -/
theorem regularIdeleClassInvariant_eq
    {L : Type u} [Field L] [NumberField L] [Algebra F L] [Algebra E L]
    [IsScalarTower F E L] [IsGalois F L]
    (c : regularIdeleClassSubgroup F E) (a : relativeIdeleCohomology F L 2)
    (ha : ideleQuotientCohomologyMap F L 2 a =
      relativeIdeleClassInflation F E L 2 c.val) :
    regularIdeleClassInvariant s hker hInf F E c = s F L a :=
  regularValue_eq s hker hInf F E c a ha

/-- On classes already represented by ideles, the regular invariant is the given map. -/
theorem regularIdeleClassInvariant_apply_quotient (a : relativeIdeleCohomology F E 2) :
    regularIdeleClassInvariant s hker hInf F E
      ⟨ideleQuotientCohomologyMap F E 2 a,
        quotient_range_le_regularIdeleClassSubgroup F E ⟨a, rfl⟩⟩ = s F E a := by
  have ha : ideleQuotientCohomologyMap F E 2 (relativeIdeleInflation F E E 2 a) =
      relativeIdeleClassInflation F E E 2 (ideleQuotientCohomologyMap F E 2 a) :=
    ConcreteCategory.congr_hom (relativeIdeleInflation_comp_quotient F E E 2) a
  exact (regularIdeleClassInvariant_eq s hker hInf F E
    (L := E) _ (relativeIdeleInflation F E E 2 a) ha).trans (hInf F E E a)

end Construction

section Inflation

variable (F E K : Type u) [Field F] [Field E] [Field K]
  [NumberField F] [NumberField E] [NumberField K]
  [Algebra F E] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
  [IsGalois F E] [IsGalois F K]

/-- Actual inflation preserves the constructed invariant on regular classes. -/
theorem regularIdeleClassInvariant_inflation (c : regularIdeleClassSubgroup F E) :
    regularIdeleClassInvariant s hker hInf F K (regularIdeleClassInflation F E K c) =
      regularIdeleClassInvariant s hker hInf F E c := by
  let d := regularIdeleClassInflation F E K c
  rcases d.property with ⟨L, _, _, _, _, _, _, a, ha⟩
  let : Algebra E L := ((algebraMap K L).comp (algebraMap E K)).toAlgebra
  let : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap F L x = algebraMap K L (algebraMap E K (algebraMap F E x))
    rw [← IsScalarTower.algebraMap_apply F E K, ← IsScalarTower.algebraMap_apply F K L]
  have haE : ideleQuotientCohomologyMap F L 2 a =
      relativeIdeleClassInflation F E L 2 c.val := by
    exact ha.trans (ideleClassInflationTransitivity F E K L 2 c.val)
  exact (regularIdeleClassInvariant_eq s hker hInf F K d a ha).trans
    (regularIdeleClassInvariant_eq s hker hInf F E c a haE).symm

end Inflation

section Restriction

variable (hRes : s.RestrictionCompatible)
  (F K E : Type u) [Field F] [Field K] [Field E]
  [NumberField F] [NumberField K] [NumberField E]
  [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
  [IsGalois F E]

include hRes in
/-- Actual restriction multiplies the constructed regular invariant by the degree. -/
theorem regularIdeleClassInvariant_restriction (c : regularIdeleClassSubgroup F E) :
    let := IsGalois.tower_top_of_isGalois F K E
    regularIdeleClassInvariant s hker hInf K E (regularIdeleClassRestriction F K E c) =
      Module.finrank F K • regularIdeleClassInvariant s hker hInf F E c := by
  dsimp only
  let := IsGalois.tower_top_of_isGalois F K E
  rcases c.property with ⟨L, _, _, _, _, _, _, a, ha⟩
  let : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap F L x = algebraMap E L (algebraMap K E (algebraMap F K x))
    rw [← IsScalarTower.algebraMap_apply F K E, ← IsScalarTower.algebraMap_apply F E L]
  let := IsGalois.tower_top_of_isGalois F K L
  have haK : ideleQuotientCohomologyMap K L 2 (relativeIdeleRestriction F K L 2 a) =
      relativeIdeleClassInflation K E L 2
        (regularIdeleClassRestriction F K E c).val := by
    calc
      _ = relativeIdeleClassRestriction F K L 2
          (ideleQuotientCohomologyMap F L 2 a) :=
        ConcreteCategory.congr_hom (relativeIdeleRestriction_comp_quotient F K L 2) a
      _ = relativeIdeleClassRestriction F K L 2
          (relativeIdeleClassInflation F E L 2 c.val) := congrArg _ ha
      _ = _ := ideleClassInflationRestrictionCompatibility F K E L 2 c.val
  rw [regularIdeleClassInvariant_eq s hker hInf K E _
      (relativeIdeleRestriction F K L 2 a) haK,
    regularIdeleClassInvariant_eq s hker hInf F E c a ha, hRes F K L]

end Restriction

end Langlands.ClassField.Global
