import Langlands.GroupScheme.IntegralModel.ScaledVectorPoints
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-! # Integer-depth vector models over a valuation ring -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hv : Function.Surjective v)

include hv in
/-- Every integer depth is attained by a nonzero scalar. -/
theorem exists_integerDepthScale (m : ℤ) :
    ∃ t : Kˣ, v (t : K) = WithZero.exp (-m) := by
  obtain ⟨x, hx⟩ := hv (WithZero.exp (-m))
  have hx0 : x ≠ 0 := by
    intro h
    have hz : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-m) := by
      simpa only [h, map_zero] using hx
    exact WithZero.exp_ne_zero hz.symm
  exact ⟨Units.mk0 x hx0, hx⟩

/-- A chosen scalar of source-positive integer depth `m`. -/
def integerDepthScale (m : ℤ) : Kˣ :=
  (exists_integerDepthScale v hv m).choose

@[simp] theorem valuation_integerDepthScale (m : ℤ) :
    v (integerDepthScale v hv m : K) = WithZero.exp (-m) :=
  (exists_integerDepthScale v hv m).choose_spec

variable (R : ValuationSubring K) (hvR : v.valuationSubring = R) (n : ℕ)

include hvR in
/-- A principal vector lattice over the valuation ring has the exact
coordinatewise multiplicative valuation bound of its scalar. -/
theorem mem_principalVectorLattice_iff_valuation_le (t : Kˣ) (w : Fin n → K) :
    w ∈ principalVectorLattice R K n (t : K) ↔
      ∀ j, v (w j) ≤ v (t : K) := by
  constructor
  · rintro ⟨a, ha⟩ j
    rw [ha j, map_mul]
    have hj : v (algebraMap R K (a j)) ≤ 1 := by
      exact (v.mem_valuationSubring_iff _).mp (hvR.symm ▸ (a j).property)
    exact (mul_le_mul_of_nonneg_left hj zero_le).trans_eq (mul_one _)
  · intro h
    have hint (j : Fin n) : w j / (t : K) ∈ R := by
      rw [← hvR, v.mem_valuationSubring_iff, v.map_div,
        div_le_one₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr (Units.ne_zero t)))]
      exact h j
    refine ⟨fun j => ⟨w j / (t : K), hint j⟩, ?_⟩
    intro j
    change w j = (t : K) * (w j / (t : K))
    field_simp

/-- The standard smooth vector model with scalar generic identification at
real depth `r`, rounded up to the integer value lattice. -/
def integerDepthVector (r : ℝ) :
    IntegralModel R K (VectorGroup.groupScheme (CommRingCat.of K) n) :=
  scaledVector R K n (integerDepthScale v hv ⌈r⌉)

include hvR in
/-- Integral points of the real-depth model are exactly the coordinate ball. -/
theorem integerDepthVector_mem_integralPoints (r : ℝ)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of K) n)) :
    g ∈ (integerDepthVector v hv R n r).integralPoints ↔
      ∀ j, v ((VectorGroup.sectionCoordinates (CommRingCat.of K) n g).toAdd j) ≤
        WithZero.exp (-⌈r⌉) := by
  rw [integerDepthVector, scaledVector_mem_integralPoints_iff_mem_principalVectorLattice,
    mem_principalVectorLattice_iff_valuation_le v R hvR,
    valuation_integerDepthScale]

include hvR in
/-- The deeper-to-shallower scale quotient is integral, including negative
and nonintegral real depths. -/
theorem integerDepthScale_div_mem {r s : ℝ} (h : r ≤ s) :
    (integerDepthScale v hv ⌈s⌉ : K) / (integerDepthScale v hv ⌈r⌉ : K) ∈ R := by
  rw [← hvR, v.mem_valuationSubring_iff, v.map_div,
    valuation_integerDepthScale, valuation_integerDepthScale,
    div_le_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)]
  exact WithZero.coe_le_coe.mpr (neg_le_neg (Int.ceil_mono h))

/-- The integral coefficient of the actual identity extension. -/
def integerDepthVectorCoefficient {r s : ℝ} (h : r ≤ s) : R :=
  ⟨(integerDepthScale v hv ⌈s⌉ : K) / (integerDepthScale v hv ⌈r⌉ : K),
    integerDepthScale_div_mem v hv R hvR h⟩

/-- The actual model map from a deeper integer-rounded vector model to a
shallower one extends the identity on the generic vector group. -/
def integerDepthVectorTransition {r s : ℝ} (h : r ≤ s) :
    (integerDepthVector v hv R n s).Hom (integerDepthVector v hv R n r) (𝟙 _) :=
  scaledVectorTransition (integerDepthScale v hv ⌈s⌉) (integerDepthScale v hv ⌈r⌉)
    (integerDepthVectorCoefficient v hv R hvR h) (by
      change (_ / (integerDepthScale v hv ⌈r⌉ : K)) * _ = _
      exact div_mul_cancel₀ _ (Units.ne_zero _))

include hvR in
/-- Every compatible identity extension has a smooth connected unipotent
actual special-fibre kernel, in every vector dimension. -/
theorem integerDepthVector_kernel_properties {r s : ℝ} (h : r ≤ s)
    (φ : (integerDepthVector v hv R n s).Hom (integerDepthVector v hv R n r) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  apply scaledVector_kernel_properties (integerDepthScale v hv ⌈s⌉)
    (integerDepthScale v hv ⌈r⌉) (integerDepthVectorCoefficient v hv R hvR h) _ φ
  change (_ / (integerDepthScale v hv ⌈r⌉ : K)) * _ = _
  exact div_mul_cancel₀ _ (Units.ne_zero _)

end Langlands.GroupScheme.IntegralModel
