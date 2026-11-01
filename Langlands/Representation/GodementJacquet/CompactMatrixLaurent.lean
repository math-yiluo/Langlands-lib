import Langlands.Representation.GodementJacquet.Zeta
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Laurent integrals of compactly supported matrix functions -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg
open scoped BigOperators

universe uX uF

section DiscreteWeight

variable {X : Type uX} [TopologicalSpace X]

/-- A compactly supported function has only finitely many nonzero discrete
orders. The order need not be a group homomorphism. -/
theorem finite_orders_of_hasCompactSupport (ord : X → ℤ) (hord : Continuous ord)
    (h : X → ℂ) (hc : HasCompactSupport h) :
    ∃ I : Finset ℤ, ∀ x, h x ≠ 0 → ord x ∈ I := by
  classical
  let S : Set ℤ := ord '' tsupport h
  have hS : S.Finite := (hc.image hord).finite_of_discrete
  refine ⟨hS.toFinset, fun x hx => ?_⟩
  exact hS.mem_toFinset.mpr ⟨x, subset_tsupport h hx, rfl⟩

variable [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

/-- The Laurent polynomial formed from the actual integrals on a finite
collection of discrete-order fibers. -/
def discreteWeightLaurent (ord : X → ℤ) (h : X → ℂ) (I : Finset ℤ) :
    LaurentCoefficients :=
  ∑ m ∈ I, LaurentPolynomial.C (∫ x, ({x | ord x = m} : Set X).indicator h x ∂μ) *
    LaurentPolynomial.T m

/-- Compact support and a continuous integer weight give an actual Laurent
polynomial integral, with absolute convergence for every complex parameter. -/
theorem exists_laurent_integral_discreteWeight (q : ℕ) (hq : 0 < q)
    (ord : X → ℤ) (hord : Continuous ord)
    (h : X → ℂ) (hh : Continuous h) (hc : HasCompactSupport h) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      Integrable (fun x => h x * spectralPoint q s ^ ord x) μ ∧
      (∫ x, h x * spectralPoint q s ^ ord x ∂μ) =
        laurentEval (spectralUnit hq s) A := by
  classical
  obtain ⟨I, hI⟩ := finite_orders_of_hasCompactSupport ord hord h hc
  let A : LaurentCoefficients := discreteWeightLaurent μ ord h I
  have hmeas (m : ℤ) : MeasurableSet ({x | ord x = m} : Set X) :=
    (isClosed_discrete ({m} : Set ℤ)).preimage hord |>.measurableSet
  have hi (m : ℤ) : Integrable (({x | ord x = m} : Set X).indicator h) μ :=
    (hh.integrable_of_hasCompactSupport hc).indicator (hmeas m)
  have heq (s : ℂ) : (fun x => h x * spectralPoint q s ^ ord x) =
      fun x => ∑ m ∈ I,
        ({x | ord x = m} : Set X).indicator h x * spectralPoint q s ^ m := by
    funext x
    by_cases hx : h x = 0
    · simp [Set.indicator_apply, hx]
    · symm
      rw [Finset.sum_eq_single (ord x)]
      · rw [Set.indicator_of_mem (show x ∈ ({y | ord y = ord x} : Set X) from rfl)]
      · intro m _ hm
        rw [Set.indicator_of_notMem (show x ∉ ({x | ord x = m} : Set X) from
          fun he => hm he.symm), zero_mul]
      · exact fun hn => (hn (hI x hx)).elim
  refine ⟨A, fun s => ⟨?_, ?_⟩⟩
  · rw [heq s]
    exact integrable_finsetSum I fun m _ => (hi m).mul_const _
  · rw [heq s, integral_finsetSum I fun m _ => (hi m).mul_const _]
    simp only [integral_mul_const, A, discreteWeightLaurent, map_sum, map_mul, laurentEval_C,
      laurentEval_T, coe_spectralUnit]

end DiscreteWeight

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance compactMatrixLaurentTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance compactMatrixLaurentValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance compactMatrixLaurentLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance compactMatrixLaurentMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance compactMatrixLaurentBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The shifted determinant weight separates into a fixed weight and an
integer power of the exact spectral point. -/
theorem determinantWeight_shift_spectral (g : Langlands.GeneralLinear (n + 1) F.Carrier)
    (s t : ℂ) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (s + t) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g t *
        spectralPoint F.canonicalTopologicalData.residueCardinality s ^
          F.canonicalTopologicalData.ord (Matrix.det g.val) := by
  rw [determinantWeight, Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr
      ((normalizedAbsoluteValue F.canonicalTopologicalData).pos g.det_ne_zero).ne')]
  rw [mul_comm]
  congr 1
  exact normalizedDeterminantWeight_eq_spectralPoint_zpow F.canonicalTopologicalData g s

/-- Every compactly supported continuous group function has an everywhere
convergent determinant Mellin transform with a Laurent polynomial value. -/
theorem exists_laurent_integral_of_hasCompactSupport
    (h : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hh : Continuous h) (hc : HasCompactSupport h) (t : ℂ) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      Integrable (fun g => h g *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (s + t))
          (generalLinearHaar F.Carrier n) ∧
      (∫ g, h g *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (s + t)
          ∂generalLinearHaar F.Carrier n) =
        laurentEval
          (spectralUnit (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s)
          A := by
  let T := F.canonicalTopologicalData
  let ord : Langlands.GeneralLinear (n + 1) F.Carrier → ℤ :=
    fun g => T.ord (Matrix.det g.val)
  have hord : Continuous ord :=
    (continuous_ord_units T).comp (T.generalLinearDeterminant (n + 1)).continuous
  have hw : Continuous (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      determinantWeight (normalizedAbsoluteValue T) g t) := by
    simp_rw [normalizedDeterminantWeight_eq_spectralPoint_zpow T]
    exact (continuous_of_discreteTopology : Continuous
      (fun m : ℤ => spectralPoint T.residueCardinality t ^ m)).comp hord
  obtain ⟨A, hA⟩ := exists_laurent_integral_discreteWeight
    (generalLinearHaar F.Carrier n) T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ord hord
    (fun g => h g * determinantWeight (normalizedAbsoluteValue T) g t)
    (hh.mul hw) hc.mul_right
  refine ⟨A, fun s => ?_⟩
  simpa only [determinantWeight_shift_spectral, mul_assoc, ord] using hA s

/-- Compactness of the test times coefficient on the group gives an exact
Laurent value and absolute convergence at every shifted parameter. -/
theorem exists_laurent_matrixIntegral_of_hasCompactSupport
    (Φ : MatrixTestFunction n F.Carrier)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport (fun g => Φ g.val * f g)) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      MatrixConverges F Φ (s + jpssShift n) f ∧
      matrixIntegral F Φ (s + jpssShift n) f =
        laurentEval
          (spectralUnit (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s)
          A := by
  exact exists_laurent_integral_of_hasCompactSupport F (fun g => Φ g.val * f g)
    ((Φ.continuous.comp Units.continuous_val).mul hf) hc (jpssShift n)

/-- The Laurent integral is an actual shifted rational value, including its
right-half-plane convergence witness and a nonvanishing denominator. -/
theorem exists_laurent_shiftedRationalValue_of_hasCompactSupport
    (Φ : MatrixTestFunction n F.Carrier)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport (fun g => Φ g.val * f g)) :
    ∃ A : LaurentCoefficients,
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) Φ f (laurentToRatFunc A) := by
  obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_of_hasCompactSupport F Φ f hf hc
  refine ⟨A, ⟨0, fun s _ => (hA s).1⟩, 0, fun s _ => ?_⟩
  obtain ⟨hd, he⟩ := laurentToRatFunc_regular_and_eval
    (spectralUnit (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s) A
  exact ⟨hd, (hA s).2.trans he.symm⟩

/-- Uniqueness of rational continuation identifies every rational value of a
compactly supported product with a Laurent polynomial. -/
theorem laurent_of_shiftedRationalValue_of_hasCompactSupport
    (Φ : MatrixTestFunction n F.Carrier)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport (fun g => Φ g.val * f g))
    (R : RationalFunctions)
    (hR : HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier n) Φ f R) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  obtain ⟨A, hA⟩ := exists_laurent_shiftedRationalValue_of_hasCompactSupport F Φ f hf hc
  exact ⟨A, hA.2.unique F.canonicalTopologicalData.residueCardinality_gt_one hR.2⟩

end Padic

end Langlands.GodementJacquet
