import Langlands.LocalFactor.Abelian.ZetaMeromorphic
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentReflection

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

@[simp] theorem laurentEvaluation_add (A B : ℤ →₀ ℂ) (s : ℂ) :
    laurentEvaluation T (A + B) s =
      laurentEvaluation T A s + laurentEvaluation T B s := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)

@[simp] theorem laurentEvaluation_zero (s : ℂ) :
    laurentEvaluation T 0 s = 0 := by simp [laurentEvaluation]

@[simp] theorem laurentEvaluation_sub (A B : ℤ →₀ ℂ) (s : ℂ) :
    laurentEvaluation T (A - B) s =
      laurentEvaluation T A s - laurentEvaluation T B s := by
  apply eq_sub_iff_add_eq.mpr
  rw [← laurentEvaluation_add, sub_add_cancel]

/-- The exponential monomial is the integral power of the spectral variable. -/
theorem spectralVariable_zpow (s : ℂ) (k : ℤ) :
    spectralVariable T s ^ k =
      Complex.exp (-(k : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
  rw [spectralVariable, ← Complex.exp_int_mul]
  congr 1
  ring

@[simp] theorem laurentEvaluation_single (k : ℤ) (c s : ℂ) :
    laurentEvaluation T (Finsupp.single k c) s = c * spectralVariable T s ^ k := by
  rw [laurentEvaluation, Finsupp.sum_single_index (by simp), spectralVariable_zpow]

theorem laurentEvaluation_finset_sum {ι : Type*} (S : Finset ι)
    (A : ι → ℤ →₀ ℂ) (s : ℂ) :
    laurentEvaluation T (∑ i ∈ S, A i) s = ∑ i ∈ S, laurentEvaluation T (A i) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [Finset.sum_insert hi, ih]

/-- Clearing a linear Euler denominator stays within finite Laurent expressions. -/
theorem exists_laurent_eulerClear (A : ℤ →₀ ℂ) (c : ℂ) :
    ∃ B : ℤ →₀ ℂ, ∀ s : ℂ, laurentEvaluation T B s =
      (1 - c * spectralVariable T s) * laurentEvaluation T A s := by
  classical
  refine ⟨A - A.sum (fun k b => Finsupp.single (k + 1) (c * b)), ?_⟩
  intro s
  rw [laurentEvaluation_sub, Finsupp.sum, laurentEvaluation_finset_sum]
  simp only [laurentEvaluation_single,
    zpow_add₀ (spectralVariable_ne_zero T s), zpow_one]
  have he : (∑ k ∈ A.support, c * A k * (spectralVariable T s ^ k * spectralVariable T s)) =
      c * spectralVariable T s * laurentEvaluation T A s := by
    rw [laurentEvaluation, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← spectralVariable_zpow]
    ring
  rw [he]
  ring

/-- Compatibility with the Library's Laurent polynomial evaluation. -/
theorem laurentEvaluation_eq_laurentEval (P : LaurentPolynomial ℂ) (s : ℂ) :
    laurentEvaluation T P.coeff s =
      RankinSelberg.laurentEval
        (RankinSelberg.spectralUnit
          (Nat.zero_lt_one.trans T.residueCardinality_gt_one) s) P := by
  have hs : RankinSelberg.spectralPoint T.residueCardinality s =
      spectralVariable T s := by
    rw [RankinSelberg.spectralPoint, Complex.cpow_def_of_ne_zero
      (by exact_mod_cast (Nat.zero_lt_one.trans T.residueCardinality_gt_one).ne')]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log
      (show (0 : ℝ) ≤ (T.residueCardinality : ℝ) by positivity)]
    exact congrArg Complex.exp (mul_comm _ _)
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [AddMonoidAlgebra.coeff_add, laurentEvaluation_add, map_add, hP, hQ]
  | C_mul_T k c =>
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      laurentEvaluation_single]
    rw [LaurentPolynomial.single_eq_C_mul_T]
    simp only [map_mul, RankinSelberg.laurentEval_C, RankinSelberg.laurentEval_T,
      RankinSelberg.coe_spectralUnit, hs]

/-- Laurent coefficients are determined by their entire spectral evaluation. -/
theorem laurentEvaluation_injective :
    Function.Injective (fun A : ℤ →₀ ℂ => laurentEvaluation T A) := by
  intro A B h
  have he : (AddMonoidAlgebra.ofCoeff A : LaurentPolynomial ℂ) =
      AddMonoidAlgebra.ofCoeff B := by
    apply RankinSelberg.TwoBlockFirstBlockLaurent.laurent_eq_of_infinite_spectral_eval_eq
      T.residueCardinality_gt_one Set.univ Set.infinite_univ
    intro t _
    simpa only [← laurentEvaluation_eq_laurentEval, AddMonoidAlgebra.coeff_ofCoeff]
      using congrFun h (t : ℂ)
  exact congrArg AddMonoidAlgebra.coeff he

/-- Agreement on one neighborhood already determines the finite coefficients. -/
theorem laurentEvaluation_eq_of_eventuallyEq {A B : ℤ →₀ ℂ} {s : ℂ}
    (h : laurentEvaluation T A =ᶠ[𝓝 s] laurentEvaluation T B) : A = B := by
  apply laurentEvaluation_injective T
  funext t
  have hA := analyticAt_laurentEvaluation T A t
  have hB := analyticAt_laurentEvaluation T B t
  have hg := meromorphic_germ_eq_of_eventuallyEq
    (fun z _ => (analyticAt_laurentEvaluation T A z).meromorphicAt)
    (fun z _ => (analyticAt_laurentEvaluation T B z).meromorphicAt) h t
  exact ((hA.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    hB.meromorphicNFAt).mp hg).eq_of_nhds

/-- The raw Euler--Laurent product is meromorphic everywhere. -/
theorem meromorphicOn_lFactor_mul_laurent (π : F.Carrierˣ) (χ : Character)
    (a : ℕ) (A : ℤ →₀ ℂ) :
    MeromorphicOn (fun s => lFactorAt T π χ a s * laurentEvaluation T A s) Set.univ :=
  (lFactorAt_meromorphicNFOn T π χ a).meromorphicOn.mul
    (fun s _ => (analyticAt_laurentEvaluation T A s).meromorphicAt)

/-- At regular points the raw Euler--Laurent product is analytic. -/
theorem analyticAt_lFactor_mul_laurent (π : F.Carrierˣ) (χ : Character)
    (a : ℕ) (A : ℤ →₀ ℂ) (s : ℂ) (hs : RegularPoint T π χ a s) :
    AnalyticAt ℂ (fun z => lFactorAt T π χ a z * laurentEvaluation T A z) s :=
  (analyticAt_lFactorAt_of_regular T π χ a s hs).mul
    (analyticAt_laurentEvaluation T A s)

/-- Normalization preserves the value of an Euler--Laurent product at every regular point. -/
theorem normalized_lFactor_mul_laurent_eq (π : F.Carrierˣ) (χ : Character)
    (a : ℕ) (A : ℤ →₀ ℂ) (s : ℂ) (hs : RegularPoint T π χ a s) :
    toMeromorphicNFOn (fun z => lFactorAt T π χ a z * laurentEvaluation T A z)
        Set.univ s = lFactorAt T π χ a s * laurentEvaluation T A s := by
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt
    (meromorphicOn_lFactor_mul_laurent T π χ a A) (Set.mem_univ s),
    toMeromorphicNFAt_eq_self.mpr
      (analyticAt_lFactor_mul_laurent T π χ a A s hs).meromorphicNFAt]

end Langlands.LocalFactor.PadicAbelian
