import Langlands.FieldTheory.HenselianSeparableDepthLattice
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.GroupTheory.Archimedean

/-! # Rings of integers of the prolonged valuation on a finite separable extension -/

noncomputable section

universe u

namespace Langlands.FieldTheory

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)
  (E : Type u) [Field E] [Algebra K E] [Algebra.IsSeparable K E]

/-- The ring of integers `{x ∈ E | w(x) ≥ 0}` of the normalized prolongation `w` of `v` to a
separable extension `E`, as a valuation subring of `E`. -/
def henselianSeparableIntegers : ValuationSubring E where
  carrier := {x | 0 ≤ henselianSeparableAddValuation v hH E x}
  mul_mem' {x y} hx hy := by
    change 0 ≤ henselianSeparableAddValuation v hH E (x * y)
    rw [AddValuation.map_mul]
    exact add_nonneg hx hy
  one_mem' := by
    change 0 ≤ henselianSeparableAddValuation v hH E 1
    rw [AddValuation.map_one]
  add_mem' {x y} hx hy :=
    le_trans (le_min hx hy) ((henselianSeparableAddValuation v hH E).map_add x y)
  zero_mem' := by
    change 0 ≤ henselianSeparableAddValuation v hH E 0
    rw [AddValuation.map_zero]
    exact le_top
  neg_mem' {x} hx := by
    change 0 ≤ henselianSeparableAddValuation v hH E (-x)
    rw [AddValuation.map_neg]
    exact hx
  mem_or_inv_mem' x := by
    change 0 ≤ henselianSeparableAddValuation v hH E x ∨
      0 ≤ henselianSeparableAddValuation v hH E x⁻¹
    rcases eq_or_ne x 0 with rfl | hx
    · left
      rw [AddValuation.map_zero]
      exact le_top
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
      ((henselianSeparableAddValuation v hH E).ne_top_iff.mpr hx)
    rw [AddValuation.map_inv, ← ht]
    rcases le_total 0 t with h | h
    · left
      exact_mod_cast h
    · right
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
      exact_mod_cast neg_nonneg.mpr h

theorem mem_henselianSeparableIntegers (x : E) :
    x ∈ henselianSeparableIntegers v hH E ↔ 0 ≤ henselianSeparableAddValuation v hH E x :=
  Iff.rfl

/-- Positive prolonged value on a base scalar is `v a < 1`. -/
theorem henselianSeparableAddValuation_base_pos_iff (a : K) :
    0 < henselianSeparableAddValuation v hH E (algebraMap K E a) ↔ v a < 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, AddValuation.map_zero, map_zero]
    exact iff_of_true (WithTop.coe_lt_top (0 : ℝ)) zero_lt_one
  · have hv0 : v a ≠ 0 := v.ne_zero_iff.mpr ha
    rw [henselianSeparableAddValuation_base v hH E ha, ← WithTop.coe_zero, WithTop.coe_lt_coe,
      Int.cast_pos, neg_pos, WithZero.log_lt_iff_lt_exp hv0, WithZero.exp_zero]

/-- The base valuation ring maps into the ring of integers of the prolongation. -/
instance henselianSeparableIntegers.algebra :
    Algebra v.valuationSubring (henselianSeparableIntegers v hH E) :=
  ((algebraMap v.valuationSubring E).codRestrict (henselianSeparableIntegers v hH E)
    (fun a => (henselianSeparableAddValuation_base_nonneg_iff v hH E (a : K)).mpr a.2)).toAlgebra

@[simp] theorem henselianSeparableIntegers.coe_algebraMap (a : v.valuationSubring) :
    ((algebraMap v.valuationSubring (henselianSeparableIntegers v hH E) a :
      henselianSeparableIntegers v hH E) : E) = algebraMap K E (a : K) :=
  rfl

instance henselianSeparableIntegers.isScalarTower :
    IsScalarTower v.valuationSubring (henselianSeparableIntegers v hH E) E :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The ring of integers is the depth-zero lattice, as a module over the base valuation ring. -/
def henselianSeparableIntegersEquivDepthLattice :
    henselianSeparableIntegers v hH E ≃ₗ[v.valuationSubring]
      henselianSeparableDepthLattice v hH E 0 where
  toFun x := ⟨x, by
    rw [mem_henselianSeparableDepthLattice, WithTop.coe_zero]
    exact x.2⟩
  invFun y := ⟨y, by
    have h := y.2
    rw [mem_henselianSeparableDepthLattice, WithTop.coe_zero] at h
    exact h⟩
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    change ((a • x : henselianSeparableIntegers v hH E) : E) = a • (x : E)
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [FiniteDimensional K E] (hv : Function.Surjective v)

include hv in
theorem henselianSeparableIntegers_finite :
    Module.Finite v.valuationSubring (henselianSeparableIntegers v hH E) := by
  have := henselianSeparableDepthLattice_finite v hH E hv 0
  exact Module.Finite.equiv (henselianSeparableIntegersEquivDepthLattice v hH E).symm

include hv in
theorem henselianSeparableIntegers_free :
    Module.Free v.valuationSubring (henselianSeparableIntegers v hH E) := by
  have := henselianSeparableDepthLattice_free v hH E hv 0
  exact Module.Free.of_equiv (henselianSeparableIntegersEquivDepthLattice v hH E).symm

omit [FiniteDimensional K E] in
/-- The maximal ideal of the ring of integers consists of the elements of positive value. -/
theorem mem_maximalIdeal_henselianSeparableIntegers (x : henselianSeparableIntegers v hH E) :
    x ∈ IsLocalRing.maximalIdeal (henselianSeparableIntegers v hH E) ↔
      0 < henselianSeparableAddValuation v hH E x := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hle
    have h0 : henselianSeparableAddValuation v hH E x = 0 :=
      le_antisymm (not_lt.mp hle) x.2
    have hx0 : (x : E) ≠ 0 := by
      intro h
      rw [h, AddValuation.map_zero] at h0
      exact WithTop.top_ne_coe h0
    have hinv : (x : E)⁻¹ ∈ henselianSeparableIntegers v hH E := by
      change 0 ≤ henselianSeparableAddValuation v hH E (x : E)⁻¹
      rw [AddValuation.map_inv, h0, neg_zero]
    exact hnu (IsUnit.of_mul_eq_one (a := x) ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0)))
  · intro hpos hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h := congrArg (fun z : henselianSeparableIntegers v hH E =>
      henselianSeparableAddValuation v hH E (z : E)) hy
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, AddValuation.map_mul,
      AddValuation.map_one] at h
    have hlt := lt_of_lt_of_le hpos (le_add_of_nonneg_right y.2)
    rw [h] at hlt
    exact lt_irrefl _ hlt

omit [FiniteDimensional K E] in
instance henselianSeparableIntegers.isLocalHom :
    IsLocalHom (algebraMap v.valuationSubring (henselianSeparableIntegers v hH E)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ IsLocalRing.maximalIdeal v.valuationSubring := hna
  rw [ValuationSubring.valuation_lt_one_iff] at hm
  have hv1 : v a < 1 := (Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one.mpr hm
  have hpos := (henselianSeparableAddValuation_base_pos_iff v hH E (a : K)).mpr hv1
  have hmem := (mem_maximalIdeal_henselianSeparableIntegers v hH E
    (algebraMap v.valuationSubring (henselianSeparableIntegers v hH E) a)).mpr hpos
  exact hmem ha

include hv in
/-- **Trivial residue extension.** If the residue field of the base is algebraically closed,
so is the residue field of the ring of integers of every finite separable extension: the
residue field extension is finite, hence trivial. -/
theorem henselianSeparableIntegers_residueField_isAlgClosed
    [IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring)] :
    IsAlgClosed (IsLocalRing.ResidueField (henselianSeparableIntegers v hH E)) := by
  have := henselianSeparableIntegers_finite v hH E hv
  have : Algebra.IsIntegral (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField (henselianSeparableIntegers v hH E)) :=
    Algebra.IsIntegral.of_finite (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField (henselianSeparableIntegers v hH E))
  exact IsAlgClosed.of_ringEquiv _ _
    (RingEquiv.ofBijective _ (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := IsLocalRing.ResidueField v.valuationSubring)
      (K := IsLocalRing.ResidueField (henselianSeparableIntegers v hH E))))

include hv in
/-- Monic integral quadratics over `E` have approximate roots in `E`, when the residue field
of the base is algebraically closed. -/
theorem henselianSeparable_exists_quadratic_approxRoot
    [IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring)] (t n : E)
    (ht : 0 ≤ henselianSeparableAddValuation v hH E t)
    (hn : 0 ≤ henselianSeparableAddValuation v hH E n) :
    ∃ b : E, 0 < henselianSeparableAddValuation v hH E (b ^ 2 - t * b + n) := by
  have := henselianSeparableIntegers_residueField_isAlgClosed v hH E hv
  let O := henselianSeparableIntegers v hH E
  let t' : O := ⟨t, ht⟩
  let n' : O := ⟨n, hn⟩
  let p : Polynomial (IsLocalRing.ResidueField O) :=
    Polynomial.C 1 * Polynomial.X ^ 2 +
      Polynomial.C (-IsLocalRing.residue O t') * Polynomial.X +
        Polynomial.C (IsLocalRing.residue O n')
  have hp : p.degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    decide
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hp
  obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective z
  refine ⟨(b' : E), ?_⟩
  have hmem : b' ^ 2 - t' * b' + n' ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_add, map_sub, map_mul, map_pow]
    simp only [p, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at hz
    linear_combination hz
  exact (mem_maximalIdeal_henselianSeparableIntegers v hH E _).mp hmem

include hv in
/-- **Integer normalization on `E`.** A positive multiple of the prolonged value takes
integer values on `E^×` and the value `1` somewhere. -/
theorem henselianSeparable_exists_integer_scale :
    ∃ c : ℝ, 0 < c ∧
      (∀ a : E, a ≠ 0 → ∃ m : ℤ, ∃ t : ℝ,
        henselianSeparableAddValuation v hH E a = (t : WithTop ℝ) ∧ c * t = m) ∧
      ∃ ϖ : E, henselianSeparableAddValuation v hH E ϖ = ((1 / c : ℝ) : WithTop ℝ) := by
  classical
  set w := henselianSeparableAddValuation v hH E
  set n : ℕ := Module.finrank K E
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr Module.finrank_pos
  let H : AddSubgroup ℤ :=
    { carrier := {m | ∃ x : E, x ≠ 0 ∧ w x = (((m : ℝ) / n : ℝ) : WithTop ℝ)}
      zero_mem' := ⟨1, one_ne_zero, by
        rw [AddValuation.map_one, Int.cast_zero, zero_div, WithTop.coe_zero]⟩
      add_mem' := by
        rintro m m' ⟨x, hx, hxm⟩ ⟨y, hy, hym⟩
        refine ⟨x * y, mul_ne_zero hx hy, ?_⟩
        rw [AddValuation.map_mul, hxm, hym, ← WithTop.coe_add, Int.cast_add, add_div]
      neg_mem' := by
        rintro m ⟨x, hx, hxm⟩
        refine ⟨x⁻¹, inv_ne_zero hx, ?_⟩
        rw [AddValuation.map_inv, hxm, ← WithTop.LinearOrderedAddCommGroup.coe_neg, Int.cast_neg, neg_div] }
  have hnH : (n : ℤ) ∈ H := by
    obtain ⟨t, ht0, ht⟩ := henselianSeparableAddValuation_exists_base_value v hH E hv 1
    refine ⟨algebraMap K E t, (map_ne_zero _).mpr ht0, ?_⟩
    rw [ht, Int.cast_natCast, div_self (ne_of_gt hn), Int.cast_one]
  obtain ⟨g, hg⟩ := Int.subgroup_cyclic H
  have hmul : ∀ m ∈ H, ∃ k : ℤ, k * g = m := by
    intro m hm
    rw [hg, AddSubgroup.mem_closure_singleton] at hm
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, by simpa only [smul_eq_mul] using hk⟩
  have hgH : g ∈ H := by
    rw [hg]
    exact AddSubgroup.subset_closure rfl
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hmul _ hnH
    rw [mul_zero] at hk
    exact (ne_of_gt hn) (by exact_mod_cast hk.symm)
  set d : ℤ := |g|
  have hdH : d ∈ H := by
    rcases abs_choice g with h | h
    · rw [show d = g from h]
      exact hgH
    · rw [show d = -g from h]
      exact H.neg_mem hgH
  have hd : (0 : ℝ) < d := by
    have : (0 : ℤ) < d := abs_pos.mpr hg0
    exact_mod_cast this
  refine ⟨n / d, div_pos hn hd, ?_, ?_⟩
  · intro a ha
    obtain ⟨m, hm⟩ := henselianSeparableAddValuation_exists_lattice_value v hH E ha
    have hmH : m ∈ H := ⟨a, ha, hm⟩
    obtain ⟨k, hk⟩ := hmul m hmH
    have hgd : (g : ℝ) = d ∨ (g : ℝ) = -d := by
      rcases abs_choice g with h | h
      · left
        rw [show d = g from h]
      · right
        rw [show d = -g from h, Int.cast_neg, neg_neg]
    rcases hgd with h | h
    · refine ⟨k, (m : ℝ) / n, hm, ?_⟩
      rw [← hk, Int.cast_mul, h]
      field_simp
    · refine ⟨-k, (m : ℝ) / n, hm, ?_⟩
      rw [← hk, Int.cast_mul, h, Int.cast_neg]
      field_simp
  · obtain ⟨ϖ, -, hϖ⟩ := hdH
    refine ⟨ϖ, ?_⟩
    rw [hϖ, one_div_div]

end Langlands.FieldTheory
