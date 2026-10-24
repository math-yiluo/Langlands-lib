import Langlands.ClassField.Global.IdeleRegularInvariant
import Langlands.ClassField.Global.IdeleAuxiliaryDescent
import Langlands.ClassField.Global.IdeleClassH2OrderStatement
import Langlands.ClassField.Global.InvariantClassConditions

/-! # Conditional assembly of the global invariant family -/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.ClassFieldTheory.Local FundamentalClass

universe u

set_option backward.isDefEq.respectTransparency false

namespace IdeleInvariantMaps

/-- On cyclic extensions, the idele maps have the full global denominator range. -/
def CyclicRange (s : IdeleInvariantMaps.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    (s F E).range = denominatorSubgroup (Module.finrank F E)

end IdeleInvariantMaps

variable (s : IdeleInvariantMaps.{u}) (hker : s.KillsQuotientKernel)
  (hInf : s.InflationCompatible)

private theorem denominator_card (n : ℕ) (hn : 0 < n) :
    Nat.card (denominatorSubgroup n) = n :=
  (Nat.card_congr (denominatorEquiv n hn).toEquiv).symm.trans (Nat.card_zmod n)

section Cyclic

variable (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- Full idele range supplies every denominator value on regular classes. -/
theorem regularIdeleClassInvariant_surjective_of_range
    (hrange : (s F E).range = denominatorSubgroup (Module.finrank F E)) :
    Function.Surjective (regularIdeleClassInvariantToDenominator F E
      (regularIdeleClassInvariant s hker hInf F E)) := by
  intro y
  have hy : y.val ∈ (s F E).range := hrange.symm ▸ y.property
  obtain ⟨a, ha⟩ := hy
  refine ⟨⟨ideleQuotientCohomologyMap F E 2 a,
    quotient_range_le_regularIdeleClassSubgroup F E ⟨a, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact (regularIdeleClassInvariant_apply_quotient s hker hInf F E a).trans ha

/-- Surjectivity and the order bound make the regular invariant injective. -/
theorem regularIdeleClassInvariant_injective_of_surjective
    [Finite (relativeIdeleClassCohomology F E 2)]
    (hcard : Nat.card (relativeIdeleClassCohomology F E 2) ≤ Module.finrank F E)
    (hs : Function.Surjective (regularIdeleClassInvariantToDenominator F E
      (regularIdeleClassInvariant s hker hInf F E))) :
    Function.Injective (regularIdeleClassInvariant s hker hInf F E) := by
  have hle : Nat.card (regularIdeleClassSubgroup F E) ≤
      Nat.card (denominatorSubgroup (Module.finrank F E)) := by
    rw [denominator_card _ Module.finrank_pos]
    exact (Nat.card_le_card_of_injective
      (regularIdeleClassSubgroup F E).subtype Subtype.val_injective).trans hcard
  have hi := (hs.bijective_of_nat_card_le hle).1
  intro a b hab
  exact hi (Subtype.ext hab)

end Cyclic

variable (hRes : s.RestrictionCompatible) (hcyc : s.CyclicRange)
  (hdesc : IdeleClassGaloisDescent.{u, u}) (hH1 : IdeleClassH1Vanishing.{u})
  (horder : IdeleClassH2OrderBound.{u, u})

include hRes hcyc hdesc hH1 horder in
/-- The cyclic input and auxiliary descent give the full range for every extension. -/
theorem regularIdeleClassInvariant_surjective
    (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [IsGalois F E] :
    Function.Surjective (regularIdeleClassInvariantToDenominator F E
      (regularIdeleClassInvariant s hker hInf F E)) := by
  let T := cyclicAuxiliaryTower F E (Module.finrank_pos : 0 < Module.finrank F E)
  let := (horder E T.overfield).1
  have hUpper : Function.Injective (regularIdeleClassInvariant s hker hInf E T.overfield) :=
    regularIdeleClassInvariant_injective_of_surjective s hker hInf E T.overfield
      (Nat.le_of_dvd Module.finrank_pos (horder E T.overfield).2)
      (regularIdeleClassInvariant_surjective_of_range s hker hInf E T.overfield
        (hcyc E T.overfield))
  have hRange : (regularIdeleClassInvariant s hker hInf F T.auxiliary).range =
      denominatorSubgroup (Module.finrank F T.auxiliary) := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact regularIdeleClassInvariant_mem_denominator F T.auxiliary _ c
    · intro hy
      obtain ⟨c, hc⟩ := regularIdeleClassInvariant_surjective_of_range
        s hker hInf F T.auxiliary (hcyc F T.auxiliary) ⟨y, hy⟩
      exact ⟨c, congrArg Subtype.val hc⟩
  exact regularIdeleClassInvariant_surjective_of_auxiliary F E T
    (regularIdeleClassInvariant s hker hInf F E)
    (regularIdeleClassInvariant s hker hInf F T.auxiliary)
    (regularIdeleClassInvariant s hker hInf F T.overfield)
    (regularIdeleClassInvariant s hker hInf E T.overfield)
    hdesc (hH1 E T.overfield)
    (regularIdeleClassInvariant_inflation s hker hInf F E T.overfield)
    (regularIdeleClassInvariant_inflation s hker hInf F T.auxiliary T.overfield)
    (regularIdeleClassInvariant_restriction s hker hInf hRes F E T.overfield)
    hUpper hRange

include hker hInf hRes hcyc hdesc hH1 horder in
/-- Every actual idele-class cohomology class is regular under the stated inputs. -/
theorem regularIdeleClassSubgroup_eq_top
    (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [IsGalois F E] :
    regularIdeleClassSubgroup F E = ⊤ := by
  let := (horder F E).1
  apply AddSubgroup.eq_top_of_le_card
  have hs := regularIdeleClassInvariant_surjective s hker hInf hRes hcyc hdesc hH1 horder F E
  have hd := denominator_card (Module.finrank F E) Module.finrank_pos
  exact (Nat.le_of_dvd Module.finrank_pos (horder F E).2).trans
    (hd ▸ Nat.card_le_card_of_surjective _ hs)

/-- The resulting invariant maps on the entire actual idele-class cohomology. -/
def assembledIdeleClassInvariantMaps : GlobalInvariantMaps.{u} := by
  intro F _ _ E _ _ _ _
  let j : relativeIdeleClassCohomology F E 2 →+ regularIdeleClassSubgroup F E :=
    { toFun := fun c => ⟨c, by
        rw [regularIdeleClassSubgroup_eq_top s hker hInf hRes hcyc hdesc hH1 horder F E]
        trivial⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact (regularIdeleClassInvariant s hker hInf F E).comp j

@[simp]
theorem assembledIdeleClassInvariantMaps_apply_regular
    (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [IsGalois F E] (c : regularIdeleClassSubgroup F E) :
    assembledIdeleClassInvariantMaps s hker hInf hRes hcyc hdesc hH1 horder F E c.val =
      regularIdeleClassInvariant s hker hInf F E c := rfl

@[simp]
theorem assembledIdeleClassInvariantMaps_apply_quotient
    (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [IsGalois F E] (a : relativeIdeleCohomology F E 2) :
    assembledIdeleClassInvariantMaps s hker hInf hRes hcyc hdesc hH1 horder F E
      (ideleQuotientCohomologyMap F E 2 a) = s F E a :=
  regularIdeleClassInvariant_apply_quotient s hker hInf F E a

/-- The assembled maps are injective and have the full denominator image. -/
theorem assembledIdeleClassInvariantMaps_images :
    InvariantImages (assembledIdeleClassInvariantMaps s hker hInf hRes hcyc hdesc hH1 horder) := by
  intro F _ _ E _ _ _ _
  let := (horder F E).1
  have hs := regularIdeleClassInvariant_surjective s hker hInf hRes hcyc hdesc hH1 horder F E
  have hi := regularIdeleClassInvariant_injective_of_surjective s hker hInf F E
    (Nat.le_of_dvd Module.finrank_pos (horder F E).2) hs
  have hreg (a : relativeIdeleClassCohomology F E 2) : IsRegularIdeleClass F E a := by
    change a ∈ regularIdeleClassSubgroup F E
    rw [regularIdeleClassSubgroup_eq_top s hker hInf hRes hcyc hdesc hH1 horder F E]
    trivial
  constructor
  · intro a b hab
    exact congrArg Subtype.val (hi (a₁ := ⟨a, hreg a⟩) (a₂ := ⟨b, hreg b⟩) hab)
  · ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact regularIdeleClassInvariant_mem_denominator F E
        (regularIdeleClassInvariant s hker hInf F E) ⟨a, hreg a⟩
    · intro hy
      obtain ⟨c, hc⟩ := hs ⟨y, hy⟩
      exact ⟨c.val, congrArg Subtype.val hc⟩

/-- Inflation preserves the assembled invariant on every class. -/
theorem assembledIdeleClassInvariantMaps_inflation :
    InvariantInflationOnClasses
      (assembledIdeleClassInvariantMaps s hker hInf hRes hcyc hdesc hH1 horder) := by
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _ a
  have ha : IsRegularIdeleClass F E a := by
    change a ∈ regularIdeleClassSubgroup F E
    rw [regularIdeleClassSubgroup_eq_top s hker hInf hRes hcyc hdesc hH1 horder F E]
    trivial
  exact regularIdeleClassInvariant_inflation s hker hInf F E L ⟨a, ha⟩

/-- Restriction multiplies the assembled invariant by the base-extension degree. -/
theorem assembledIdeleClassInvariantMaps_restriction :
    InvariantRestrictionOnClasses
      (assembledIdeleClassInvariantMaps s hker hInf hRes hcyc hdesc hH1 horder) := by
  intro F K E _ _ _ _ _ _ _ _ _ _ _ a
  let := IsGalois.tower_top_of_isGalois F K E
  have ha : IsRegularIdeleClass F E a := by
    change a ∈ regularIdeleClassSubgroup F E
    rw [regularIdeleClassSubgroup_eq_top s hker hInf hRes hcyc hdesc hH1 horder F E]
    trivial
  exact regularIdeleClassInvariant_restriction s hker hInf hRes F K E ⟨a, ha⟩

end Langlands.ClassField.Global
