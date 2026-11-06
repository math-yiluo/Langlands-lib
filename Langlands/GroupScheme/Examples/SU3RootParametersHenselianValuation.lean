import Langlands.FieldTheory.HenselianIntegerAddValuation
import Langlands.GroupScheme.Examples.SU3RootParametersLocalValuation
import Langlands.Geometry.Building.IntegerValuation

/-! # Quadratic SU3 coordinates over henselian integer-valued fields -/

noncomputable section

open Algebra

universe u v

namespace Langlands.GroupScheme.SU3Root

variable (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
  [IsQuadraticExtension F L] [Algebra.IsSeparable F L]
  (v : Valuation F (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

local instance : FiniteDimensional F L :=
  .of_finrank_pos (by rw [IsQuadraticExtension.finrank_eq_two F L]; decide)

/-- The invariant extension value with the base integer normalization. -/
def henselianQuadraticValuation : AddValuation L (WithTop ℝ) :=
  FieldTheory.henselianIntegerAddValuation v hH L

@[simp] theorem henselianQuadraticValuation_conjugation (x : L) :
    henselianQuadraticValuation F L v hH (conjugation F L x) =
      henselianQuadraticValuation F L v hH x :=
  FieldTheory.henselianIntegerAddValuation_invariant v hH L (conjugation F L) x

@[simp] theorem henselianQuadraticValuation_bar (x : L) :
    henselianQuadraticValuation F L v hH ((fieldInvolution F L).bar x) =
      henselianQuadraticValuation F L v hH x :=
  henselianQuadraticValuation_conjugation F L v hH x

theorem henselianQuadraticValuation_base {a : F} (ha : a ≠ 0) :
    henselianQuadraticValuation F L v hH (algebraMap F L a) =
      (((-WithZero.log (v a) : ℤ) : ℝ) : WithTop ℝ) :=
  FieldTheory.henselianIntegerAddValuation_base v hH L ha

/-- The restriction agrees with the order used by the actual integer apartment. -/
theorem henselianQuadraticValuation_base_unit (a : Fˣ) :
    henselianQuadraticValuation F L v hH (algebraMap F L (a : F)) =
      ((Geometry.Building.IntegerValuation.order v a : ℝ) : WithTop ℝ) := by
  rw [henselianQuadraticValuation_base F L v hH (Units.ne_zero a),
    Geometry.Building.IntegerValuation.order,
    Geometry.Building.IntegerValuation.orderUnits_toAdd]

/-- Nonzero values are half-integers, without a surjectivity assertion. -/
theorem henselianQuadraticValuation_exists_half_integer {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, henselianQuadraticValuation F L v hH x = ((n : ℝ) / 2 : ℝ) := by
  simpa only [henselianQuadraticValuation, IsQuadraticExtension.finrank_eq_two,
    Nat.cast_ofNat] using
    FieldTheory.henselianIntegerAddValuation_exists_lattice_value v hH L hx

theorem henselianQuadraticValuation_norm (x : L) :
    henselianQuadraticValuation F L v hH (algebraMap F L (Algebra.norm F x)) =
      2 • henselianQuadraticValuation F L v hH x := by
  simpa only [henselianQuadraticValuation, IsQuadraticExtension.finrank_eq_two] using
    FieldTheory.henselianIntegerAddValuation_norm v hH L x

/-- The embedded field trace cannot decrease the value. -/
theorem henselianQuadraticValuation_le_trace (x : L) :
    henselianQuadraticValuation F L v hH x ≤
      henselianQuadraticValuation F L v hH
        (algebraMap F L (Algebra.trace F L x)) := by
  rw [algebraMap_trace]
  exact (henselianQuadraticValuation F L v hH).map_le_add le_rfl
    (by rw [henselianQuadraticValuation_conjugation])

variable (hv : Function.Surjective v)

include hv

/-- Every base integer order occurs on a nonzero embedded scalar. -/
theorem exists_henselianQuadraticValuation_base_eq (n : ℤ) :
    ∃ a : F, a ≠ 0 ∧ henselianQuadraticValuation F L v hH
      (algebraMap F L a) = ((n : ℝ) : WithTop ℝ) := by
  obtain ⟨a, ha⟩ := hv (WithZero.exp (-n))
  have ha0 : a ≠ 0 := by
    intro h
    have h0 : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-n) := by
      simpa only [h, map_zero] using ha
    exact WithZero.exp_ne_zero h0.symm
  refine ⟨a, ha0, ?_⟩
  rw [henselianQuadraticValuation_base F L v hH ha0, ha, WithZero.log_exp, neg_neg]

/-- Nonzero trace-zero coordinates realize every integer translate of their value. -/
theorem henselianQuadraticValuation_traceZero_integer_translate
    (z : Parameters.traceZero (fieldInvolution F L)) (hz : (z : L) ≠ 0) (n : ℤ) :
    ∃ w : Parameters.traceZero (fieldInvolution F L), (w : L) ≠ 0 ∧
      henselianQuadraticValuation F L v hH (w : L) = ((n : ℝ) : WithTop ℝ) +
        henselianQuadraticValuation F L v hH (z : L) := by
  obtain ⟨a, ha, hn⟩ := exists_henselianQuadraticValuation_base_eq F L v hH hv n
  have hmem : algebraMap F L a * (z : L) ∈
      Parameters.traceZero (fieldInvolution F L) := by
    change algebraMap F L a * (z : L) +
      conjugation F L (algebraMap F L a * (z : L)) = 0
    rw [map_mul, AlgEquiv.commutes, ← mul_add]
    exact mul_eq_zero_of_right _ z.property
  refine ⟨⟨algebraMap F L a * (z : L), hmem⟩,
    mul_ne_zero ((map_ne_zero _).mpr ha) hz, ?_⟩
  change henselianQuadraticValuation F L v hH (algebraMap F L a * (z : L)) = _
  rw [AddValuation.map_mul, hn]

/-- Nontrivial central parameters have second-coordinate values above any real bound. -/
theorem exists_henselian_central_parameter_of_value_ge (r : ℝ) :
    ∃ p : rationalParameters F L,
      p ∈ Parameters.central (fieldInvolution F L) ∧ p.second ≠ 0 ∧
        (r : WithTop ℝ) ≤ henselianQuadraticValuation F L v hH p.second := by
  obtain ⟨z, hz⟩ := exists_ne_zero_traceZero F L
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
    ((henselianQuadraticValuation F L v hH).ne_top_iff.mpr hz)
  obtain ⟨n, hn⟩ := exists_int_ge (r - c)
  obtain ⟨w, hw, hval⟩ :=
    henselianQuadraticValuation_traceZero_integer_translate F L v hH hv z hz n
  have hp : (w : L) + (fieldInvolution F L).bar (w : L) =
      (0 : L) * (fieldInvolution F L).bar 0 := by
    rw [zero_mul]
    exact w.property
  refine ⟨⟨(0, (w : L)), hp⟩, rfl, hw, ?_⟩
  change (r : WithTop ℝ) ≤ henselianQuadraticValuation F L v hH (w : L)
  rw [hval, ← hc, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

end Langlands.GroupScheme.SU3Root
