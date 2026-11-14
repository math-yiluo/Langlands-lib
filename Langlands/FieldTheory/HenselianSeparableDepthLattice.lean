import Langlands.FieldTheory.HenselianSeparableIntegerAddValuation
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Order.Floor.Ring

/-! # Actual valuation-depth lattices in finite separable extensions -/

noncomputable section

universe u v

namespace Langlands.FieldTheory

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)
  (L : Type v) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The field trace cannot decrease the normalized additive value. -/
theorem henselianSeparableAddValuation_le_trace [FiniteDimensional K L] (x : L) :
    henselianSeparableAddValuation v hH L x ≤
      henselianSeparableAddValuation v hH L (algebraMap K L (Algebra.trace K L x)) := by
  classical
  let Ω := SeparableClosure K
  let f : L →ₐ[K] Ω := IsSepClosed.lift
  let w := henselianIntegerAddValuation v hH Ω
  have hs : ((minpoly K x).map (algebraMap K Ω)).Splits :=
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)
  have hval : ∀ y ∈ (minpoly K x).aroots Ω, w y = w (f x) := by
    intro y hy
    apply henselianIntegerAddValuation_eq_of_minpoly_eq
    apply minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic (R := K) (f x))
    rw [minpoly.algHom_eq f f.injective]
    exact (Polynomial.mem_aroots.mp hy).2
  have hsum : ∀ s : Multiset Ω, (∀ y ∈ s, w (f x) ≤ w y) →
      w (f x) ≤ w s.sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | @cons y s ih =>
        intro h
        rw [Multiset.sum_cons]
        exact w.map_le_add (h y (by simp)) (ih (fun z hz => h z (by simp [hz])))
  have hnsmul : ∀ n : ℕ, w (f x) ≤ w (n • ((minpoly K x).aroots Ω).sum) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [succ_nsmul]
        exact w.map_le_add ih (hsum _ (fun y hy => (hval y hy).ge))
  rw [henselianSeparableAddValuation_apply v hH L f,
    henselianSeparableAddValuation_apply v hH L f, f.commutes,
    trace_eq_sum_roots hs]
  exact hnsmul _

/-- Integral base scalars are exactly the scalars with nonnegative prolonged value. -/
theorem henselianSeparableAddValuation_base_nonneg_iff (x : K) :
    0 ≤ henselianSeparableAddValuation v hH L (algebraMap K L x) ↔
      x ∈ v.valuationSubring := by
  by_cases hx : x = 0
  · simp [hx]
  rw [henselianSeparableAddValuation_base v hH L hx, ← WithTop.coe_zero,
    WithTop.coe_le_coe, v.mem_valuationSubring_iff]
  have hlog : WithZero.log (v x) ≤ 0 ↔ v x ≤ 1 := by
    rw [WithZero.log_le_iff_le_exp (v.ne_zero_iff.mpr hx), WithZero.exp_zero]
  constructor
  · intro h
    apply hlog.mp
    have : (0 : ℤ) ≤ -WithZero.log (v x) := by exact_mod_cast h
    omega
  · intro h
    have : (0 : ℤ) ≤ -WithZero.log (v x) := neg_nonneg.mpr (hlog.mpr h)
    exact_mod_cast this

/-- The actual additive valuation ball, as a module over the base valuation ring. -/
def henselianSeparableDepthLattice (r : ℝ) : Submodule v.valuationSubring L where
  carrier := {x | (r : WithTop ℝ) ≤ henselianSeparableAddValuation v hH L x}
  zero_mem' := by simp
  add_mem' hx hy := (henselianSeparableAddValuation v hH L).map_le_add hx hy
  smul_mem' a x hx := by
    change (r : WithTop ℝ) ≤ henselianSeparableAddValuation v hH L (a • x)
    rw [← IsScalarTower.algebraMap_smul K a x, Algebra.smul_def, AddValuation.map_mul]
    have ha : 0 ≤ henselianSeparableAddValuation v hH L (algebraMap K L (a : K)) :=
      (henselianSeparableAddValuation_base_nonneg_iff v hH L _).mpr a.property
    exact hx.trans ((le_add_of_nonneg_left ha))

@[simp]
theorem mem_henselianSeparableDepthLattice (r : ℝ) (x : L) :
    x ∈ henselianSeparableDepthLattice v hH L r ↔
      (r : WithTop ℝ) ≤ henselianSeparableAddValuation v hH L x := Iff.rfl

/-- Increasing the requested depth gives a sublattice. -/
theorem henselianSeparableDepthLattice_antitone :
    Antitone (henselianSeparableDepthLattice v hH L) := by
  intro r s hrs x hx
  exact (WithTop.coe_le_coe.mpr hrs).trans hx

variable (hv : Function.Surjective v)

include hv in
/-- A surjective integer valuation has a discrete valuation ring. -/
theorem integerValuationSubring_isDiscreteValuationRing :
    IsDiscreteValuationRing v.valuationSubring := by
  let : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    WithZero.unitsWithZeroEquiv.isCyclic.mpr inferInstance
  have hg : MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass v) = ⊤ := by
    apply top_unique
    intro a _
    exact MonoidWithZeroHom.mem_valueGroup _ (hv (a : WithZero (Multiplicative ℤ)))
  let : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass v)) := by
    rw [hg]
    infer_instance
  exact Valuation.valuationSubring_isDiscreteValuationRing v

include hv in
/-- The normalized prolongation attains every integer on the base field. -/
theorem henselianSeparableAddValuation_exists_base_value (m : ℤ) :
    ∃ t : K, t ≠ 0 ∧
      henselianSeparableAddValuation v hH L (algebraMap K L t) = ((m : ℝ) : WithTop ℝ) := by
  obtain ⟨t, ht⟩ := hv (WithZero.exp (-m))
  have ht0 : t ≠ 0 := by
    intro h
    have : WithZero.exp (-m) = (0 : WithZero (Multiplicative ℤ)) := by
      simpa only [h, map_zero] using ht.symm
    exact WithZero.exp_ne_zero this
  refine ⟨t, ht0, ?_⟩
  rw [henselianSeparableAddValuation_base v hH L ht0, ht]
  simp

include hv in
/-- A single base denominator makes the trace coefficient of every element
of the actual depth ball integral. -/
theorem henselianSeparableDepthLattice_trace_denominator [FiniteDimensional K L]
    (r : ℝ) {b : L} (hb : b ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ ∀ x ∈ henselianSeparableDepthLattice v hH L r,
      Algebra.trace K L (x * b) / t ∈ v.valuationSubring := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
    ((henselianSeparableAddValuation v hH L).ne_top_iff.mpr hb)
  obtain ⟨t, ht0, ht⟩ :=
    henselianSeparableAddValuation_exists_base_value v hH L hv ⌊r + c⌋
  refine ⟨t, ht0, ?_⟩
  intro x hx
  change (r : WithTop ℝ) ≤ henselianSeparableAddValuation v hH L x at hx
  apply (henselianSeparableAddValuation_base_nonneg_iff v hH L _).mp
  rw [map_div₀, AddValuation.map_div, ht]
  have hbound :
      (((⌊r + c⌋ : ℤ) : ℝ) : WithTop ℝ) ≤
        henselianSeparableAddValuation v hH L
          (algebraMap K L (Algebra.trace K L (x * b))) := by
    calc
      _ ≤ ((r + c : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.mpr (Int.floor_le _)
      _ ≤ henselianSeparableAddValuation v hH L (x * b) := by
        rw [AddValuation.map_mul, ← hc, WithTop.coe_add]
        exact add_le_add hx le_rfl
      _ ≤ _ := henselianSeparableAddValuation_le_trace v hH L _
  by_cases hz : Algebra.trace K L (x * b) = 0
  · simp [hz]
  have hz' : algebraMap K L (Algebra.trace K L (x * b)) ≠ 0 := by
    intro h
    apply hz
    apply (algebraMap K L).injective
    simpa only [map_zero] using h
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp
    ((henselianSeparableAddValuation v hH L).ne_top_iff.mpr hz')
  rw [← hd, WithTop.coe_le_coe] at hbound
  rw [← hd, ← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_zero,
    WithTop.coe_le_coe]
  exact sub_nonneg.mpr hbound

include hv in
/-- Trace-dual expansion places the actual depth ball inside the span of
a finite family of scaled field vectors. -/
theorem henselianSeparableDepthLattice_le_finite_span [FiniteDimensional K L] (r : ℝ) :
    ∃ n : ℕ, ∃ z : Fin n → L,
      henselianSeparableDepthLattice v hH L r ≤
        Submodule.span v.valuationSubring (Set.range z) := by
  classical
  let b := Module.finBasis K L
  choose t ht0 ht using fun j =>
    henselianSeparableDepthLattice_trace_denominator v hH L hv r (b.ne_zero j)
  let z := fun j => algebraMap K L (t j) * b.traceDual j
  refine ⟨Module.finrank K L, z, ?_⟩
  intro x hx
  let a : Fin (Module.finrank K L) → v.valuationSubring :=
    fun j => ⟨Algebra.trace K L (x * b j) / t j, ht j x hx⟩
  have hexp : x = ∑ j, a j • z j := by
    rw [← b.traceDual.sum_repr x]
    apply Finset.sum_congr rfl
    intro j _
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
    change Algebra.trace K L (x * b j) • b.traceDual j =
      (a j) • (algebraMap K L (t j) * b.traceDual j)
    rw [← IsScalarTower.algebraMap_smul K (a j), Algebra.smul_def, Algebra.smul_def]
    change algebraMap K L (Algebra.trace K L (x * b j)) * b.traceDual j =
      algebraMap K L (Algebra.trace K L (x * b j) / t j) *
        (algebraMap K L (t j) * b.traceDual j)
    rw [← mul_assoc, ← map_mul, div_mul_cancel₀ _ (ht0 j)]
  rw [hexp]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

include hv in
/-- The actual depth lattice is finite over the base valuation ring. -/
theorem henselianSeparableDepthLattice_finite [FiniteDimensional K L]
    (r : ℝ) :
    Module.Finite v.valuationSubring (henselianSeparableDepthLattice v hH L r) := by
  let := integerValuationSubring_isDiscreteValuationRing v hv
  obtain ⟨n, z, hz⟩ := henselianSeparableDepthLattice_le_finite_span v hH L hv r
  exact Module.Finite.iff_fg.mpr
    ((Submodule.fg_span (Set.finite_range z)).of_le hz)

include hv in
/-- Each actual depth lattice is a finite free module over the base valuation ring. -/
theorem henselianSeparableDepthLattice_free [FiniteDimensional K L]
    (r : ℝ) :
    Module.Free v.valuationSubring (henselianSeparableDepthLattice v hH L r) := by
  let := integerValuationSubring_isDiscreteValuationRing v hv
  let := henselianSeparableDepthLattice_finite v hH L hv r
  exact Module.free_of_finite_type_torsion_free'

include hv in
/-- Every extension-field element can be moved into any depth ball by a
nonzero integral base scalar. -/
theorem henselianSeparableDepthLattice_exists_smul (r : ℝ) (x : L) :
    ∃ a : v.valuationSubring, a ≠ 0 ∧
      a • x ∈ henselianSeparableDepthLattice v hH L r := by
  by_cases hx : x = 0
  · exact ⟨1, one_ne_zero, by simp [hx]⟩
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp
    ((henselianSeparableAddValuation v hH L).ne_top_iff.mpr hx)
  let m : ℤ := ⌈max 0 (r - d)⌉
  have hm0 : (0 : ℝ) ≤ m := (le_max_left _ _).trans (Int.le_ceil _)
  have hmr : r - d ≤ m := (le_max_right _ _).trans (Int.le_ceil _)
  obtain ⟨t, ht0, ht⟩ := henselianSeparableAddValuation_exists_base_value v hH L hv m
  have hint : t ∈ v.valuationSubring := by
    apply (henselianSeparableAddValuation_base_nonneg_iff v hH L t).mp
    rw [ht, ← WithTop.coe_zero, WithTop.coe_le_coe]
    exact hm0
  refine ⟨⟨t, hint⟩, ?_, ?_⟩
  · intro h
    exact ht0 (congrArg (fun a : v.valuationSubring => (a : K)) h)
  · change (r : WithTop ℝ) ≤ henselianSeparableAddValuation v hH L
      ((⟨t, hint⟩ : v.valuationSubring) • x)
    rw [← IsScalarTower.algebraMap_smul K (⟨t, hint⟩ : v.valuationSubring) x,
      Algebra.smul_def]
    change (r : WithTop ℝ) ≤
      henselianSeparableAddValuation v hH L (algebraMap K L t * x)
    rw [AddValuation.map_mul, ht, ← hd, ← WithTop.coe_add, WithTop.coe_le_coe]
    linarith

include hv in
/-- The actual depth ball spans the whole extension over the base field. -/
theorem henselianSeparableDepthLattice_span (r : ℝ) :
    Submodule.span K (henselianSeparableDepthLattice v hH L r : Set L) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, hax⟩ := henselianSeparableDepthLattice_exists_smul v hH L hv r x
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply ha
    exact Subtype.ext h
  have h := (Submodule.span K
    (henselianSeparableDepthLattice v hH L r : Set L)).smul_mem (a : K)⁻¹
      (Submodule.subset_span hax)
  rw [← IsScalarTower.algebraMap_smul K a x] at h
  change (a : K)⁻¹ • ((a : K) • x) ∈ _ at h
  rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h
  exact h

end Langlands.FieldTheory
