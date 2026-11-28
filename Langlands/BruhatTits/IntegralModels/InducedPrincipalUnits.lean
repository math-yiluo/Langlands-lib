import Langlands.BruhatTits.IntegralModels.InducedTorusShallowIntegers
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Jacobson.Ideal

/-! # The principal-unit difference map in induced torus coordinates -/

noncomputable section

universe u

open Langlands.LocalField Langlands.LocalGalois.Separable Langlands.Geometry.Building
open scoped NNReal

namespace Langlands.BruhatTits.IntegralModels

namespace WeilCongruence

variable {C : Type*} [CommRing C]

/-- The coefficient units reducing to one modulo `J`. -/
def principalUnits (J : Ideal C) : Subgroup Cˣ :=
  (Units.map (Ideal.Quotient.mk J).toMonoidHom).ker

@[simp] theorem mem_principalUnits (J : Ideal C) (w : Cˣ) :
    w ∈ principalUnits J ↔ (w : C) - 1 ∈ J := by
  change Units.map (Ideal.Quotient.mk J).toMonoidHom w = 1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk J (w : C) = 1 ↔ _
  rw [← (Ideal.Quotient.mk J).map_one]
  exact Ideal.Quotient.eq

variable (J L : Ideal C)

local notation "Q" => J ⧸ Submodule.comap (Submodule.subtype J) L

/-- Taking the difference from one is a homomorphism modulo `L` when `J * J ≤ L`. -/
def principalUnitDifference (h : J * J ≤ L) : principalUnits J →* Multiplicative (Q) where
  toFun w := Multiplicative.ofAdd (Submodule.Quotient.mk
    ⟨(w.val : C) - 1, (mem_principalUnits J w.val).mp w.property⟩)
  map_one' := by
    change Multiplicative.ofAdd (Submodule.Quotient.mk (⟨(1 : C) - 1, _⟩ : J) : Q) = 1
    apply congrArg Multiplicative.ofAdd
    rw [Submodule.Quotient.mk_eq_zero]
    change (1 : C) - 1 ∈ L
    simp
  map_mul' w z := by
    change Multiplicative.ofAdd
        (Submodule.Quotient.mk (⟨(w.val : C) * z.val - 1, _⟩ : J) : Q) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (⟨(w.val : C) - 1, _⟩ : J) +
        Submodule.Quotient.mk (⟨(z.val : C) - 1, _⟩ : J))
    apply congrArg Multiplicative.ofAdd
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    change ((w.val : C) * z.val - 1) - (((w.val : C) - 1) + ((z.val : C) - 1)) ∈ L
    rw [show ∀ a b : C, a * b - 1 - ((a - 1) + (b - 1)) = (a - 1) * (b - 1) by
      intro a b
      ring]
    exact Ideal.mul_le.mp h _ ((mem_principalUnits J w.val).mp w.property)
      _ ((mem_principalUnits J z.val).mp z.property)

private theorem principalUnitDifference_ker (h : J * J ≤ L) :
    (principalUnitDifference J L h).ker = (principalUnits L).subgroupOf (principalUnits J) := by
  ext w
  change Multiplicative.ofAdd (Submodule.Quotient.mk (⟨(w.val : C) - 1, _⟩ : J) : Q) = 1 ↔
    w.val ∈ principalUnits L
  rw [← Multiplicative.toAdd.injective.eq_iff]
  change Submodule.Quotient.mk (⟨(w.val : C) - 1, _⟩ : J) = (0 : Q) ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_principalUnits]
  rfl

private theorem principalUnitDifference_surjective (h : J * J ≤ L)
    (hJ : J ≤ Ideal.jacobson ⊥) : Function.Surjective (principalUnitDifference J L h) := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
    (Submodule.comap (Submodule.subtype J) L) (Multiplicative.toAdd y)
  have hmem : (1 : C) + x.val - 1 ∈ J := by simp
  have hu : IsUnit (1 + x.val) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ hmem)
  have hw : (↑hu.unit : C) - 1 = x.val := by rw [IsUnit.unit_spec, add_sub_cancel_left]
  let w : principalUnits J := ⟨hu.unit, (mem_principalUnits J _).mpr (hw.symm ▸ x.property)⟩
  have hwx : (⟨(w.val : C) - 1, (mem_principalUnits J _).mp w.property⟩ : J) = x :=
    Subtype.ext hw
  exact ⟨w, congrArg Multiplicative.ofAdd
    ((congrArg (Submodule.Quotient.mk : J → Q) hwx).trans hx)⟩

/-- The principal-unit quotient is the additive ideal quotient via `w ↦ w - 1`. -/
def principalUnitDifferenceEquiv (h : J * J ≤ L) (hJ : J ≤ Ideal.jacobson ⊥) :
    (principalUnits J ⧸ (principalUnits L).subgroupOf (principalUnits J)) ≃* Multiplicative (Q) :=
  (QuotientGroup.quotientMulEquivOfEq (principalUnitDifference_ker J L h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (principalUnitDifference J L h)
      (principalUnitDifference_surjective J L h hJ))

@[simp] theorem principalUnitDifferenceEquiv_mk (h : J * J ≤ L) (hJ : J ≤ Ideal.jacobson ⊥)
    (w : principalUnits J) :
    principalUnitDifferenceEquiv J L h hJ (QuotientGroup.mk w) =
      Multiplicative.ofAdd (Submodule.Quotient.mk
        (⟨(w.val : C) - 1, (mem_principalUnits J w.val).mp w.property⟩ : J)) := rfl

end WeilCongruence

namespace InducedTorusShallow

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {I : Type u} (E : I → IntermediateField (inertiaFixedField F) (SeparableClosure F))

local notation "C" => productIntegers F E
local notation "ν" => algebraicExtensionAddValuation F (SeparableClosure F)

private theorem depthIdeal_mul_le {r s : ℝ≥0} (hs : s ≤ 2 * r) :
    depthIdeal F E r * depthIdeal F E r ≤ depthIdeal F E s := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  apply (mem_depthIdeal F E s _).mpr
  intro i
  change ((s : ℝ) : WithTop ℝ) ≤ ν ((x i : E i) * (y i : E i))
  rw [AddValuation.map_mul]
  apply le_trans _ (add_le_add ((mem_depthIdeal F E r _).mp hx i)
    ((mem_depthIdeal F E r _).mp hy i))
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  exact_mod_cast (show s ≤ r + r from by rwa [← two_mul])

private theorem depthIdeal_le_jacobson {r : ℝ≥0} (hr : 0 < r) :
    depthIdeal F E r ≤ Ideal.jacobson (⊥ : Ideal C) := by
  intro x hx
  apply Ideal.mem_jacobson_bot.mpr
  intro y
  refine Pi.isUnit_iff.mpr (fun i => (ConnectedImage.isUnit_integers_iff F (E i) _).mpr ?_)
  have hxy := (mem_depthIdeal F E r (x * y)).mp ((depthIdeal F E r).mul_mem_right y hx) i
  have hv : (0 : WithTop ℝ) < ν (((x * y) i : E i) : SeparableClosure F) :=
    lt_of_lt_of_le (by exact_mod_cast hr) hxy
  have hlt : intermediateValuation F (E i) ((x * y) i : E i) < 1 := by
    rw [intermediateValuation_apply, ← (sepClosureValuation F).map_one, lt_iff_not_ge]
    intro h
    apply hv.not_ge
    rw [← AddValuation.map_one ν]
    exact (logAdditiveValuation_le_iff _ _ _ _ _).mpr h
  change intermediateValuation F (E i) (((x * y) i : E i) + 1) = 1
  rw [← (intermediateValuation F (E i)).map_one] at hlt ⊢
  exact (intermediateValuation F (E i)).map_add_eq_of_lt_right hlt

/-- The difference isomorphism in the coefficient ideals of an induced torus.
For `r ≤ s`, the denominator consists of the depth-`s` units and the additive
denominator is the depth-`s` ideal viewed inside the depth-`r` ideal. -/
def depthPrincipalUnitEquiv (r s : ℝ≥0) (hr : 0 < r) (hs : s ≤ 2 * r) :
    (WeilCongruence.principalUnits (depthIdeal F E r) ⧸
      (WeilCongruence.principalUnits (depthIdeal F E s)).subgroupOf
        (WeilCongruence.principalUnits (depthIdeal F E r))) ≃*
      Multiplicative (depthIdeal F E r ⧸
        Submodule.comap (Submodule.subtype (depthIdeal F E r)) (depthIdeal F E s)) :=
  WeilCongruence.principalUnitDifferenceEquiv _ _ (depthIdeal_mul_le F E hs)
    (depthIdeal_le_jacobson F E hr)

@[simp] theorem depthPrincipalUnitEquiv_mk (r s : ℝ≥0) (hr : 0 < r) (hs : s ≤ 2 * r)
    (w : WeilCongruence.principalUnits (depthIdeal F E r)) :
    depthPrincipalUnitEquiv F E r s hr hs (QuotientGroup.mk w) =
      Multiplicative.ofAdd (Submodule.Quotient.mk
        (⟨(w.val : C) - 1, (WeilCongruence.mem_principalUnits _ w.val).mp w.property⟩ :
          depthIdeal F E r)) :=
  WeilCongruence.principalUnitDifferenceEquiv_mk _ _ _ _ w

end InducedTorusShallow
end Langlands.BruhatTits.IntegralModels
