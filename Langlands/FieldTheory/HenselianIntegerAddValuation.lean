import Langlands.FieldTheory.IntegerValuationRealization
import Langlands.FieldTheory.HenselianRealGaloisProlongationProof
import Langlands.LocalField.LogAdditiveValuation
import Mathlib.RingTheory.Norm.Transitivity

/-! # Integer-normalized additive valuations over Henselian fields -/

noncomputable section

universe u v

open scoped NNReal

namespace Langlands.FieldTheory

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)
  (L : Type v) [Field L] [Algebra K L] [IsGalois K L]

include hH in
/-- A normalized invariant real prolongation of the supplied integer valuation. -/
theorem exists_integerRealProlongation :
    ∃ w : Valuation L ℝ≥0,
      w.comap (algebraMap K L) = integerValuationToReal v ∧
      ∀ (σ : L ≃ₐ[K] L) (x : L), w (σ x) = w x := by
  have hH' : HenselianLocalRing (integerValuationToReal v).valuationSubring := by
    rwa [integerValuationToReal_valuationSubring]
  exact henselianRealGaloisProlongation K (integerValuationToReal v) hH' L

/-- A chosen invariant prolongation, with exponential base two. -/
def henselianIntegerRealValuation : Valuation L ℝ≥0 :=
  (exists_integerRealProlongation v hH L).choose

@[simp] theorem henselianIntegerRealValuation_comap :
    (henselianIntegerRealValuation v hH L).comap (algebraMap K L) =
      integerValuationToReal v :=
  (exists_integerRealProlongation v hH L).choose_spec.1

@[simp] theorem henselianIntegerRealValuation_invariant
    (σ : L ≃ₐ[K] L) (x : L) :
    henselianIntegerRealValuation v hH L (σ x) =
      henselianIntegerRealValuation v hH L x :=
  (exists_integerRealProlongation v hH L).choose_spec.2 σ x

/-- The additive prolongation, normalized to the positive base integer order. -/
def henselianIntegerAddValuation : AddValuation L (WithTop ℝ) :=
  LocalField.logAdditiveValuation (henselianIntegerRealValuation v hH L)
    (Real.log 2) (Real.log_pos (by norm_num))

@[simp] theorem henselianIntegerAddValuation_invariant
    (σ : L ≃ₐ[K] L) (x : L) :
    henselianIntegerAddValuation v hH L (σ x) =
      henselianIntegerAddValuation v hH L x :=
  LocalField.logAdditiveValuation_invariant _ _ _
    σ (henselianIntegerRealValuation_invariant v hH L σ) x

/-- On every nonzero base element the additive value is its negative integer logarithm. -/
theorem henselianIntegerAddValuation_base {x : K} (hx : x ≠ 0) :
    henselianIntegerAddValuation v hH L (algebraMap K L x) =
      (((-WithZero.log (v x) : ℤ) : ℝ) : WithTop ℝ) := by
  rw [henselianIntegerAddValuation,
    LocalField.logAdditiveValuation_of_ne_zero _ _ _
      ((map_ne_zero _).mpr hx)]
  have hw : henselianIntegerRealValuation v hH L (algebraMap K L x) =
      integerValuationToReal v x :=
    DFunLike.congr_fun (henselianIntegerRealValuation_comap v hH L) x
  rw [hw, integerValuationToReal_apply,
    WithZeroMulInt.toNNReal_neg_apply _ (v.ne_zero_iff.mpr hx),
    NNReal.coe_zpow, Real.log_zpow, WithZero.toAdd_unzero_eq_log,
    Int.cast_neg]
  congr 1
  field_simp
  norm_num

/-- The actual field norm multiplies the additive value by the extension degree. -/
theorem henselianIntegerAddValuation_norm [FiniteDimensional K L] (x : L) :
    henselianIntegerAddValuation v hH L (algebraMap K L (Algebra.norm K x)) =
      Module.finrank K L • henselianIntegerAddValuation v hH L x := by
  classical
  let w := henselianIntegerAddValuation v hH L
  have hprod (s : Finset (L ≃ₐ[K] L)) :
      w (∏ σ ∈ s, σ x) = s.card • w x := by
    induction s using Finset.induction_on with
    | empty => simp [w]
    | @insert σ s hσ ih =>
        rw [Finset.prod_insert hσ, AddValuation.map_mul,
          henselianIntegerAddValuation_invariant v hH L, ih,
          Finset.card_insert_of_notMem hσ]
        simp [add_nsmul, add_comm, w]
  rw [Algebra.norm_eq_prod_automorphisms]
  simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank] using hprod Finset.univ

/-- Nonzero values lie in the inverse-degree integer lattice. -/
theorem henselianIntegerAddValuation_exists_lattice_value [FiniteDimensional K L]
    {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, henselianIntegerAddValuation v hH L x =
      ((n : ℝ) / Module.finrank K L : ℝ) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    ((henselianIntegerAddValuation v hH L).ne_top_iff.mpr hx)
  have hn := henselianIntegerAddValuation_norm v hH L x
  rw [henselianIntegerAddValuation_base v hH L
    (Algebra.norm_ne_zero_iff.mpr hx), ← hr, ← WithTop.coe_nsmul, WithTop.coe_inj,
    nsmul_eq_mul] at hn
  refine ⟨-WithZero.log (v (Algebra.norm K x)), ?_⟩
  rw [← hr]
  congr 1
  exact (eq_div_iff (Nat.cast_ne_zero.mpr
    (ne_of_gt (Module.finrank_pos (R := K) (M := L))))).mpr
      (by simpa only [mul_comm] using hn.symm)

end Langlands.FieldTheory
