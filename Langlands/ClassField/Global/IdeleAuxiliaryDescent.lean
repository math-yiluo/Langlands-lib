import Langlands.ClassField.Global.CyclicAuxiliaryTower
import Langlands.ClassField.Global.IdeleClassInflationExactness
import Langlands.ClassField.Global.IdeleRegularFunctoriality
import Langlands.ClassField.Global.IdeleInvariantDescent

/-! # Conditional descent along a cyclic auxiliary tower -/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.ClassFieldTheory.Local

universe u

variable (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- Any additive invariant on the actual regular subgroup is killed by the
extension degree. This uses cohomological annihilation, without a cardinality bound. -/
theorem regularIdeleClassInvariant_mem_denominator
    (s : regularIdeleClassSubgroup F E →+ RationalModIntegers)
    (c : regularIdeleClassSubgroup F E) :
    s c ∈ denominatorSubgroup (Module.finrank F E) := by
  have hc : Module.finrank F E • c = 0 := by
    apply Subtype.ext
    change Module.finrank F E • c.val = 0
    rw [← IsGalois.card_aut_eq_finrank F E]
    exact card_nsmul_H2_eq_zero (relativeIdeleClassRepresentation F E) c.val
  change Module.finrank F E • s c = 0
  rw [← map_nsmul, hc, map_zero]

/-- The denominator-valued form of an additive invariant on regular classes. -/
def regularIdeleClassInvariantToDenominator
    (s : regularIdeleClassSubgroup F E →+ RationalModIntegers) :
    regularIdeleClassSubgroup F E →+ denominatorSubgroup (Module.finrank F E) :=
  s.codRestrict _ (regularIdeleClassInvariant_mem_denominator F E s)

@[simp]
theorem regularIdeleClassInvariantToDenominator_coe
    (s : regularIdeleClassSubgroup F E →+ RationalModIntegers)
    (c : regularIdeleClassSubgroup F E) :
    (regularIdeleClassInvariantToDenominator F E s c : RationalModIntegers) = s c := rfl

section Auxiliary

variable (T : CyclicAuxiliaryTower F E (Module.finrank F E))
  (sE : regularIdeleClassSubgroup F E →+ RationalModIntegers)
  (sK : regularIdeleClassSubgroup F T.auxiliary →+ RationalModIntegers)
  (sL : regularIdeleClassSubgroup F T.overfield →+ RationalModIntegers)
  (sUpper : regularIdeleClassSubgroup E T.overfield →+ RationalModIntegers)
  (hdesc : IdeleClassGaloisDescent.{u, u})
  (hH1 : Subsingleton (relativeIdeleClassCohomology E T.overfield 1))
  (hE : ∀ c, sL (regularIdeleClassInflation F E T.overfield c) = sE c)
  (hK : ∀ c, sL (regularIdeleClassInflation F T.auxiliary T.overfield c) = sK c)
  (hRes : ∀ c, sUpper (regularIdeleClassRestriction F E T.overfield c) =
    Module.finrank F E • sL c)
  (hUpper : Function.Injective sUpper)
  (hRange : sK.range = denominatorSubgroup (Module.finrank F T.auxiliary))

include hdesc hH1 hE hK hRes hUpper hRange in
/-- Compatible regular invariants, the cyclic auxiliary range and upper
injectivity give every denominator value over the original field. -/
theorem regularIdeleClassInvariant_surjective_of_auxiliary :
    Function.Surjective (regularIdeleClassInvariantToDenominator F E sE) := by
  intro y
  have hy : y.val ∈ sK.range := by
    rw [hRange, T.degree]
    exact y.property
  obtain ⟨cK, hcK⟩ := hy
  let cL := regularIdeleClassInflation F T.auxiliary T.overfield cK
  have hsL : sL cL = y.val := (hK cK).trans hcK
  have hzero : regularIdeleClassRestriction F E T.overfield cL = 0 := by
    apply hUpper
    rw [hRes, hsL, map_zero]
    exact y.property
  have hkernel : cL.val ∈ LinearMap.ker
      (relativeIdeleClassRestriction F E T.overfield 2).hom := by
    exact congrArg Subtype.val hzero
  rw [← (ideleClassH2InflationExactness_of F E T.overfield hdesc hH1).2] at hkernel
  obtain ⟨c, hc⟩ := hkernel
  have hregular : IsRegularIdeleClass F E c :=
    (isRegularIdeleClass_inflation_iff F E T.overfield c).1 (hc ▸ cL.property)
  let cE : regularIdeleClassSubgroup F E := ⟨c, hregular⟩
  have hCE : regularIdeleClassInflation F E T.overfield cE = cL := Subtype.ext hc
  refine ⟨cE, Subtype.ext ?_⟩
  change sE cE = y.val
  rw [← hE cE, hCE, hsL]

variable [Finite (relativeIdeleClassCohomology F E 2)]
  (hcard : Nat.card (relativeIdeleClassCohomology F E 2) ≤ Module.finrank F E)

include hdesc hH1 hE hK hRes hUpper hRange hcard in
/-- The same auxiliary descent and the cohomology order bound make every class regular. -/
theorem regularIdeleClassSubgroup_eq_top_of_auxiliary :
    regularIdeleClassSubgroup F E = ⊤ := by
  apply AddSubgroup.eq_top_of_le_card
  have hs := regularIdeleClassInvariant_surjective_of_auxiliary
    F E T sE sK sL sUpper hdesc hH1 hE hK hRes hUpper hRange
  have hd : Nat.card (denominatorSubgroup (Module.finrank F E)) = Module.finrank F E :=
    (Nat.card_congr (denominatorEquiv _ Module.finrank_pos).toEquiv).symm.trans
      (Nat.card_zmod _)
  exact hcard.trans (hd ▸ Nat.card_le_card_of_surjective _ hs)

/-- Under the conditional auxiliary descent hypotheses and the cohomology
order bound, the regular invariant extends to an equivalence on actual `H²`. -/
def ideleClassInvariantEquivOfAuxiliary :
    relativeIdeleClassCohomology F E 2 ≃+
      denominatorSubgroup (Module.finrank F E) :=
  Langlands.FiniteInvariantDescent.equiv
    (regularIdeleClassSubgroup F E).subtype
    (regularIdeleClassInvariantToDenominator F E sE)
    (by
      intro c hc
      have hc0 : c = 0 := Subtype.ext hc
      rw [hc0]
      exact map_zero _)
    (regularIdeleClassInvariant_surjective_of_auxiliary
      F E T sE sK sL sUpper hdesc hH1 hE hK hRes hUpper hRange)
    (by
      have hd : Nat.card (denominatorSubgroup (Module.finrank F E)) = Module.finrank F E :=
        (Nat.card_congr (denominatorEquiv _ Module.finrank_pos).toEquiv).symm.trans
          (Nat.card_zmod _)
      rwa [hd])

/-- The extended equivalence agrees with the supplied invariant on regular classes. -/
@[simp]
theorem ideleClassInvariantEquivOfAuxiliary_apply_regular
    (c : regularIdeleClassSubgroup F E) :
    ideleClassInvariantEquivOfAuxiliary
      F E T sE sK sL sUpper hdesc hH1 hE hK hRes hUpper hRange hcard c.val =
        regularIdeleClassInvariantToDenominator F E sE c :=
  Langlands.FiniteInvariantDescent.equiv_apply _ _ _ _ _ c

end Auxiliary

end Langlands.ClassField.Global
