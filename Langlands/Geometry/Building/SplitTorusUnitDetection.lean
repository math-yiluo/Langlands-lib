import Langlands.Geometry.Building.RegularUnitExistence
import Langlands.Geometry.Building.KPWeilRestrictionUnitKernel
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Function detection by bounded points of split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The subgroup of field units of valuation one. -/
def valuationOneUnits (v : Valuation k Γ₀) : Subgroup kˣ :=
  (Units.map v.toMonoidHom).ker

@[simp] theorem mem_valuationOneUnits (v : Valuation k Γ₀) (x : kˣ) :
    x ∈ valuationOneUnits v ↔ v (x : k) = 1 := by
  simp only [valuationOneUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
    Units.val_one]
  rfl

/-- No nonzero integer annihilates every valuation-one unit when the residue field is
infinite. -/
theorem eq_zero_of_forall_valuationOneUnits_zpow_eq_one (v : Valuation k Γ₀)
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] (d : ℤ)
    (h : ∀ x : valuationOneUnits v, (x : kˣ) ^ d = 1) : d = 0 := by
  by_contra hd
  obtain ⟨c, hc, hp⟩ := exists_unit_valuation_pow_sub_one_eq_one v {d.natAbs}
    (by simpa using Int.natAbs_pos.mpr hd)
  have hc' : c ∈ valuationOneUnits v := (mem_valuationOneUnits v c).mpr hc
  have hh := congrArg (fun z : kˣ => (z : k)) ((pow_natAbs_eq_one).mpr (h ⟨c, hc'⟩))
  have hp' := hp d.natAbs (Finset.mem_singleton_self _)
  have hz : (c : k) ^ d.natAbs - 1 = 0 := by simpa [sub_eq_zero] using hh
  rw [hz, map_zero] at hp'
  exact zero_ne_one hp'

namespace SplitTorusUnitDetection

variable (v : Valuation k Γ₀)
variable (I : Type u) [Fintype I] [DecidableEq I]

/-- The character of valuation-one coordinate tuples given by an exponent vector. -/
def unitMonomial (m : I → ℤ) : (I → valuationOneUnits v) →* k where
  toFun t := (splitTorus.exponentValue I (fun i => (t i : kˣ))
    (Multiplicative.ofAdd m) : k)
  map_one' := by simp [splitTorus.exponentValue]
  map_mul' t s := by
    simp [splitTorus.exponentValue, mul_zpow, Finset.prod_mul_distrib]

theorem unitMonomial_mulSingle (m : I → ℤ) (i : I) (x : valuationOneUnits v) :
    unitMonomial v I m (Pi.mulSingle i x) = ((x : kˣ) ^ m i : kˣ) := by
  change ((∏ j, ((Pi.mulSingle i x : I → valuationOneUnits v) j : kˣ) ^ m j : kˣ) : k) = _
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

/-- Distinct exponent vectors remain distinct on valuation-one tuples. -/
theorem unitMonomial_injective
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] :
    Function.Injective (unitMonomial v I) := by
  intro m n h
  funext i
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_valuationOneUnits_zpow_eq_one v
  intro x
  have hx := congrArg (fun f : (I → valuationOneUnits v) →* k =>
    f (Pi.mulSingle i x)) h
  have he : (x : kˣ) ^ m i = (x : kˣ) ^ n i := by
    apply Units.ext
    simpa only [unitMonomial_mulSingle] using hx
  rw [zpow_sub, he, mul_inv_cancel]

/-- Evaluations on valuation-one tuples detect every Laurent polynomial. -/
theorem eq_zero_of_evaluateUnits_eq_zero
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)]
    (p : AddMonoidAlgebra k (I → ℤ))
    (hp : ∀ t : I → valuationOneUnits v,
      splitTorus.evaluateUnits (R := CommRingCat.of k) I (fun i => (t i : kˣ)) p = 0) :
    p = 0 := by
  have hi : LinearIndependent k (fun m : I → ℤ =>
      (unitMonomial v I m : (I → valuationOneUnits v) → k)) :=
    (linearIndependent_monoidHom (I → valuationOneUnits v) k).comp _
      (unitMonomial_injective v I)
  apply AddMonoidAlgebra.coeff_injective
  apply (linearIndependent_iff.mp hi) p.coeff
  funext t
  have he : (Finsupp.linearCombination k
      (fun m : I → ℤ => (unitMonomial v I m : (I → valuationOneUnits v) → k))
      p.coeff) t =
      splitTorus.evaluateUnits (R := CommRingCat.of k) I (fun i => (t i : kˣ)) p := by
    clear hp
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp [hp, hq]
    | single m r =>
      rw [splitTorus.evaluateUnits_single (R := CommRingCat.of k)]
      simp [unitMonomial]
  simpa [he] using hp t

end SplitTorusUnitDetection

end Langlands.Geometry.Building
