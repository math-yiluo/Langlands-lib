import Langlands.GroupScheme.Examples.SU3RootParametersRational
import Langlands.LocalField.FiniteGaloisExtensionValuation

/-! # Actual quadratic local-field valuation and central root coordinates -/

noncomputable section

open Algebra

universe u v

namespace Langlands.GroupScheme.SU3Root

variable (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
  [IsQuadraticExtension F L] [Algebra.IsSeparable F L]

local instance : FiniteDimensional F L :=
  .of_finrank_pos (by rw [IsQuadraticExtension.finrank_eq_two F L]; decide)

/-- The trace kernel of an actual separable quadratic extension is nonzero,
including in characteristic two. -/
theorem exists_ne_zero_traceZero :
    ∃ z : Parameters.traceZero (fieldInvolution F L), (z : L) ≠ 0 := by
  have hm : ∃ x : L, conjugation F L x ≠ x := by
    by_contra! h
    apply conjugation_ne_one F L
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hm
  have hz : x - conjugation F L x ∈ Parameters.traceZero (fieldInvolution F L) := by
    change (x - conjugation F L x) + conjugation F L (x - conjugation F L x) = 0
    rw [map_sub, conjugation_involutive]
    ring
  exact ⟨⟨x - conjugation F L x, hz⟩, sub_ne_zero.mpr hx.symm⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The actual extension valuation, with the base field's normalized integer order. -/
def quadraticValuation : AddValuation L (WithTop ℝ) :=
  LocalField.algebraicExtensionAddValuation F L

@[simp] theorem quadraticValuation_conjugation (x : L) :
    quadraticValuation F L (conjugation F L x) = quadraticValuation F L x :=
  LocalField.algebraicExtensionAddValuation_invariant F L (conjugation F L) x

@[simp] theorem quadraticValuation_bar (x : L) :
    quadraticValuation F L ((fieldInvolution F L).bar x) = quadraticValuation F L x :=
  quadraticValuation_conjugation F L x

omit [Algebra.IsSeparable F L] in
theorem quadraticValuation_base_unit (a : Fˣ) :
    quadraticValuation F L (algebraMap F L (a : F)) =
      (((Plancherel.fieldOrderUnits F a).toAdd : ℝ) : WithTop ℝ) :=
  LocalField.algebraicExtensionAddValuation_base_unit F L a

/-- Quadratic extension values lie in the half-integers; surjectivity onto them
is not asserted. -/
theorem quadraticValuation_exists_half_integer {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, quadraticValuation F L x = ((n : ℝ) / 2 : ℝ) := by
  simpa only [quadraticValuation, IsQuadraticExtension.finrank_eq_two, Nat.cast_ofNat] using
    LocalField.algebraicExtensionAddValuation_exists_lattice_value F L hx

theorem quadraticValuation_norm (x : L) :
    quadraticValuation F L (algebraMap F L (Algebra.norm F x)) =
      2 • quadraticValuation F L x := by
  simpa only [quadraticValuation, IsQuadraticExtension.finrank_eq_two] using
    LocalField.algebraicExtensionAddValuation_norm F L x

/-- Taking the actual field trace cannot decrease the normalized extension value. -/
theorem quadraticValuation_le_trace (x : L) :
    quadraticValuation F L x ≤
      quadraticValuation F L (algebraMap F L (Algebra.trace F L x)) := by
  rw [algebraMap_trace]
  exact (quadraticValuation F L).map_le_add le_rfl
    (by rw [quadraticValuation_conjugation])

/-- A nonzero trace-zero coordinate has nonzero base scalar multiples at every
integer translate of its value. -/
theorem quadraticValuation_traceZero_integer_translate
    (z : Parameters.traceZero (fieldInvolution F L)) (hz : (z : L) ≠ 0) (n : ℤ) :
    ∃ w : Parameters.traceZero (fieldInvolution F L), (w : L) ≠ 0 ∧
      quadraticValuation F L (w : L) = ((n : ℝ) : WithTop ℝ) +
        quadraticValuation F L (z : L) := by
  obtain ⟨a, ha, hn⟩ := FML.ord_surjective_nonzero F n
  have hmem : algebraMap F L a * (z : L) ∈
      Parameters.traceZero (fieldInvolution F L) := by
    change algebraMap F L a * (z : L) +
      conjugation F L (algebraMap F L a * (z : L)) = 0
    rw [map_mul, AlgEquiv.commutes, ← mul_add]
    exact mul_eq_zero_of_right _ z.property
  refine ⟨⟨algebraMap F L a * (z : L), hmem⟩,
    mul_ne_zero ((map_ne_zero _).mpr ha) hz, ?_⟩
  change quadraticValuation F L (algebraMap F L a * (z : L)) = _
  rw [AddValuation.map_mul]
  congr 1
  exact LocalField.algebraicExtensionAddValuation_base_of_ord_eq F L hn

/-- Nontrivial central coordinate parameters occur above every real value bound. -/
theorem exists_central_parameter_of_value_ge (r : ℝ) :
    ∃ p : rationalParameters F L,
      p ∈ Parameters.central (fieldInvolution F L) ∧ p.second ≠ 0 ∧
        (r : WithTop ℝ) ≤ quadraticValuation F L p.second := by
  obtain ⟨z, hz⟩ := exists_ne_zero_traceZero F L
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
    ((quadraticValuation F L).ne_top_iff.mpr hz)
  obtain ⟨n, hn⟩ := exists_int_ge (r - c)
  obtain ⟨w, hw, hv⟩ := quadraticValuation_traceZero_integer_translate F L z hz n
  have hp : (w : L) + (fieldInvolution F L).bar (w : L) =
      (0 : L) * (fieldInvolution F L).bar 0 := by
    rw [zero_mul]
    exact w.property
  refine ⟨⟨(0, (w : L)), hp⟩, rfl, hw, ?_⟩
  change (r : WithTop ℝ) ≤ quadraticValuation F L (w : L)
  rw [hv, ← hc, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

end Langlands.GroupScheme.SU3Root
