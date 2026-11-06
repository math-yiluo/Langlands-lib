import Langlands.FieldTheory.HenselianSeparableIntegerAddValuation
import Langlands.GroupScheme.Examples.SU3RootParametersLocalValuation
import Langlands.GroupScheme.Examples.SU3RootFiltration
import Langlands.Geometry.Building.IntegerValuation
import Mathlib.Data.Set.Card

/-! # Quadratic root depths normalized on the original henselian base field -/

noncomputable section

open Algebra

universe u v w

namespace Langlands.GroupScheme.SU3Root

variable (k : Type u) (E : Type v) (L : Type w)
  [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
  [IsQuadraticExtension E L] [Algebra.IsSeparable E L] [Algebra.IsSeparable k L]
  (v : Valuation k (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

local instance : FiniteDimensional E L :=
  .of_finrank_pos (by rw [IsQuadraticExtension.finrank_eq_two E L]; decide)

/-- Quadratic conjugation fixes the base, so it preserves the original
base-normalized separable extension valuation. -/
theorem henselianSeparableAddValuation_quadratic_bar (x : L) :
    FieldTheory.henselianSeparableAddValuation v hH L ((fieldInvolution E L).bar x) =
      FieldTheory.henselianSeparableAddValuation v hH L x :=
  FieldTheory.henselianSeparableAddValuation_invariant v hH L
    ((conjugation E L).restrictScalars k) x

/-- The unshifted multipliable-root depth, normalized on k rather than E. -/
def towerDepth (p : rationalParameters E L) : WithTop ℝ :=
  Parameters.depthA (FieldTheory.henselianSeparableAddValuation v hH L) p

/-- The depth of the literal central subgroup, with the same k-normalization. -/
def towerCentralDepth (z : Parameters.central (fieldInvolution E L)) : WithTop ℝ :=
  Parameters.depthDouble (FieldTheory.henselianSeparableAddValuation v hH L) z

omit [Algebra k E] [IsScalarTower k E L] in
@[simp] theorem towerDepth_eq_top_iff (p : rationalParameters E L) :
    towerDepth k E L v hH p = ⊤ ↔ p = 1 :=
  Parameters.depthA_eq_top_iff _ _

omit [Algebra k E] [IsScalarTower k E L] in
@[simp] theorem towerCentralDepth_eq_top_iff
    (z : Parameters.central (fieldInvolution E L)) :
    towerCentralDepth k E L v hH z = ⊤ ↔ z = 1 :=
  Parameters.depthDouble_eq_top_iff _ _

@[simp] theorem towerDepth_inv (p : rationalParameters E L) :
    towerDepth k E L v hH p⁻¹ = towerDepth k E L v hH p :=
  Parameters.depthA_inv _ (henselianSeparableAddValuation_quadratic_bar k E L v hH) p

@[simp] theorem towerCentralDepth_inv
    (z : Parameters.central (fieldInvolution E L)) :
    towerCentralDepth k E L v hH z⁻¹ = towerCentralDepth k E L v hH z :=
  Parameters.depthDouble_inv _ (henselianSeparableAddValuation_quadratic_bar k E L v hH) z

omit [Algebra k E] [IsScalarTower k E L] in
/-- Literal doubling on the actual central coordinate subgroup. -/
theorem towerCentralDepth_eq_double
    (z : Parameters.central (fieldInvolution E L)) :
    towerCentralDepth k E L v hH z = doubleTop (towerDepth k E L v hH z.val) :=
  Parameters.depthDouble_eq_double_depthA _ z

/-- An embedded base unit has exactly the original integer apartment order. -/
theorem towerValuation_base_unit (a : kˣ) :
    FieldTheory.henselianSeparableAddValuation v hH L (algebraMap k L (a : k)) =
      ((Geometry.Building.IntegerValuation.order v a : ℝ) : WithTop ℝ) := by
  rw [FieldTheory.henselianSeparableAddValuation_base v hH L (Units.ne_zero a),
    Geometry.Building.IntegerValuation.order,
    Geometry.Building.IntegerValuation.orderUnits_toAdd]

/-- The root filtration with the original base normalization. -/
def towerFiltration (r : ℝ) : Subgroup (rationalParameters E L) :=
  Parameters.filtration (FieldTheory.henselianSeparableAddValuation v hH L)
    (henselianSeparableAddValuation_quadratic_bar k E L v hH) r

/-- The central filtration as a subgroup of the full parameter group. -/
def towerCentralFiltration (r : ℝ) : Subgroup (rationalParameters E L) :=
  Parameters.centralFiltration (FieldTheory.henselianSeparableAddValuation v hH L)
    (henselianSeparableAddValuation_quadratic_bar k E L v hH) r

theorem mem_towerFiltration_iff_depth (r : ℝ) (p : rationalParameters E L) :
    p ∈ towerFiltration k E L v hH r ↔ (r : WithTop ℝ) ≤ towerDepth k E L v hH p :=
  Parameters.mem_filtration_iff_depth _
    (henselianSeparableAddValuation_quadratic_bar k E L v hH) r p

theorem mem_towerCentralFiltration_iff_depth (r : ℝ)
    (z : Parameters.central (fieldInvolution E L)) :
    z.val ∈ towerCentralFiltration k E L v hH r ↔
      (r : WithTop ℝ) ≤ towerCentralDepth k E L v hH z :=
  Parameters.mem_centralFiltration_iff_depth _
    (henselianSeparableAddValuation_quadratic_bar k E L v hH) r z

/-- The double-root level is the literal central intersection with the root level. -/
theorem towerCentralFiltration_double_eq_inf (r : ℝ) :
    towerCentralFiltration k E L v hH (2 * r) =
      Parameters.central (fieldInvolution E L) ⊓ towerFiltration k E L v hH r :=
  Parameters.centralFiltration_double_eq_inf _
    (henselianSeparableAddValuation_quadratic_bar k E L v hH) r

/-- The central commutator estimate uses the same original normalization. -/
theorem commutator_mem_towerCentralFiltration (r s : ℝ) (p q : rationalParameters E L)
    (hp : p ∈ towerFiltration k E L v hH r) (hq : q ∈ towerFiltration k E L v hH s) :
    p * q * p⁻¹ * q⁻¹ ∈ towerCentralFiltration k E L v hH (r + s) :=
  Parameters.commutator_mem_centralFiltration _
    (henselianSeparableAddValuation_quadratic_bar k E L v hH) r s p q hp hq

section Surjective

variable (hv : Function.Surjective v)

include hv in
/-- Every base integer occurs on a nonzero embedded scalar. -/
theorem exists_towerValuation_base_eq (n : ℤ) :
    ∃ a : k, a ≠ 0 ∧ FieldTheory.henselianSeparableAddValuation v hH L
      (algebraMap k L a) = ((n : ℝ) : WithTop ℝ) := by
  obtain ⟨a, ha⟩ := hv (WithZero.exp (-n))
  have ha0 : a ≠ 0 := by
    intro h
    have h0 : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-n) := by
      simpa only [h, map_zero] using ha
    exact WithZero.exp_ne_zero h0.symm
  refine ⟨a, ha0, ?_⟩
  rw [FieldTheory.henselianSeparableAddValuation_base v hH L ha0,
    ha, WithZero.log_exp, neg_neg]

include hv in
/-- A single nonzero trace-zero line gives integer translates of central
values and half of those values for the multipliable root. -/
theorem exists_towerDepth_integer_translates :
    ∃ c : ℝ, ∀ n : ℤ, ∃ z : Parameters.central (fieldInvolution E L),
      z ≠ 1 ∧ towerCentralDepth k E L v hH z = (((n : ℝ) + c : ℝ) : WithTop ℝ) ∧
        towerDepth k E L v hH z.val = ((((n : ℝ) + c) / 2 : ℝ) : WithTop ℝ) := by
  obtain ⟨z, hz⟩ := exists_ne_zero_traceZero E L
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
    ((FieldTheory.henselianSeparableAddValuation v hH L).ne_top_iff.mpr hz)
  refine ⟨c, fun n => ?_⟩
  obtain ⟨a, ha, hn⟩ := exists_towerValuation_base_eq k L v hH hv n
  have hbar : (fieldInvolution E L).bar (algebraMap k L a) = algebraMap k L a :=
    ((conjugation E L).restrictScalars k).commutes a
  have hmem : algebraMap k L a * (z : L) ∈ Parameters.traceZero (fieldInvolution E L) := by
    change algebraMap k L a * (z : L) +
      (fieldInvolution E L).bar (algebraMap k L a * (z : L)) = 0
    rw [map_mul, hbar, ← mul_add]
    exact mul_eq_zero_of_right _ z.property
  let p : rationalParameters E L := ⟨(0, algebraMap k L a * (z : L)), by
    change algebraMap k L a * (z : L) +
      (fieldInvolution E L).bar (algebraMap k L a * (z : L)) = 0 * _
    rw [zero_mul]
    exact hmem⟩
  have hp : p ∈ Parameters.central (fieldInvolution E L) := rfl
  have hp0 : p.second ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr ha) hz
  have hval : FieldTheory.henselianSeparableAddValuation v hH L p.second =
      (((n : ℝ) + c : ℝ) : WithTop ℝ) := by
    change FieldTheory.henselianSeparableAddValuation v hH L
      (algebraMap k L a * (z : L)) = _
    rw [AddValuation.map_mul, hn, ← hc, ← WithTop.coe_add]
  refine ⟨⟨p, hp⟩, ?_, hval, ?_⟩
  · intro h
    exact hp0 ((Parameters.second_eq_zero_iff p).mpr (congrArg Subtype.val h))
  · change halfTop (FieldTheory.henselianSeparableAddValuation v hH L p.second) = _
    rw [hval, halfTop_coe]

include hv in
/-- Both root-value images are infinite, with no value-lattice surjectivity claim. -/
theorem towerDepth_image_infinite :
    (Set.range (towerDepth k E L v hH)).Infinite ∧
      (Set.range (towerCentralDepth k E L v hH)).Infinite := by
  obtain ⟨c, htrans⟩ := exists_towerDepth_integer_translates k E L v hH hv
  have hinj : Function.Injective (fun n : ℤ => ((((n : ℝ) + c) / 2 : ℝ) : WithTop ℝ)) := by
    intro m n h
    have he : (m : ℝ) = (n : ℝ) := by
      have := WithTop.coe_injective h
      linarith
    exact_mod_cast he
  have hinj' : Function.Injective (fun n : ℤ => (((n : ℝ) + c : ℝ) : WithTop ℝ)) := by
    intro m n h
    have he : (m : ℝ) = (n : ℝ) := by
      have := WithTop.coe_injective h
      linarith
    exact_mod_cast he
  constructor
  · apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨n, rfl⟩
    obtain ⟨z, _, _, hza⟩ := htrans n
    exact ⟨z.val, hza⟩
  · apply (Set.infinite_range_of_injective hinj').mono
    rintro _ ⟨n, rfl⟩
    obtain ⟨z, _, hzd, _⟩ := htrans n
    exact ⟨z, hzd⟩

include hv in
/-- Arbitrarily prescribed root and central thresholds have a common
nonidentity central parameter. -/
theorem exists_ne_one_mem_towerFiltrations (r s : ℝ) :
    ∃ p : rationalParameters E L, p ≠ 1 ∧
      p ∈ towerFiltration k E L v hH r ∧ p ∈ towerCentralFiltration k E L v hH s := by
  obtain ⟨c, htrans⟩ := exists_towerDepth_integer_translates k E L v hH hv
  obtain ⟨n, hn⟩ := exists_int_ge (max (2 * r) s - c)
  obtain ⟨z, hz, hzd, hza⟩ := htrans n
  have hr : r ≤ ((n : ℝ) + c) / 2 := by
    have := le_max_left (2 * r) s
    linarith
  have hs : s ≤ (n : ℝ) + c := by
    have := le_max_right (2 * r) s
    linarith
  refine ⟨z.val, (fun h => hz (Subtype.ext h)), ?_, ?_⟩
  · rw [mem_towerFiltration_iff_depth, hza]
    exact WithTop.coe_le_coe.mpr hr
  · rw [mem_towerCentralFiltration_iff_depth, hzd]
    exact WithTop.coe_le_coe.mpr hs

end Surjective

section Finite

variable [FiniteDimensional k E]


/-- Finite multipliable-root depths lie in the inverse twice-total-degree
integer lattice. This asserts containment, not surjectivity. -/
theorem towerDepth_exists_lattice_value {p : rationalParameters E L} (hp : p ≠ 1) :
    ∃ n : ℤ, towerDepth k E L v hH p =
      ((n : ℝ) / (2 * Module.finrank k L) : ℝ) := by
  let : FiniteDimensional k L := FiniteDimensional.trans k E L
  have hp0 : p.second ≠ 0 := by
    intro h
    exact hp ((Parameters.second_eq_zero_iff p).mp h)
  obtain ⟨n, hn⟩ := FieldTheory.henselianSeparableAddValuation_exists_lattice_value v hH L hp0
  refine ⟨n, ?_⟩
  change halfTop (FieldTheory.henselianSeparableAddValuation v hH L p.second) = _
  rw [hn, halfTop_coe]
  congr 1
  ring

/-- Finite central depths lie in the inverse total-degree integer lattice. -/
theorem towerCentralDepth_exists_lattice_value
    {z : Parameters.central (fieldInvolution E L)} (hz : z ≠ 1) :
    ∃ n : ℤ, towerCentralDepth k E L v hH z =
      ((n : ℝ) / Module.finrank k L : ℝ) := by
  let : FiniteDimensional k L := FiniteDimensional.trans k E L
  have hz0 : z.val.second ≠ 0 := by
    intro h
    exact hz (Subtype.ext ((Parameters.second_eq_zero_iff z.val).mp h))
  exact FieldTheory.henselianSeparableAddValuation_exists_lattice_value v hH L hz0

end Finite

end Langlands.GroupScheme.SU3Root
