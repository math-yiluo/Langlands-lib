import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.Representation.Whittaker.ModelKirillovProof
import Langlands.Representation.Whittaker.WhittakerTypeKirillovProof

/-! # Unit membership in every actual unequal-rank JPSS zeta span -/

noncomputable section

namespace Langlands.RankinSelberg.UnitSpanAssembly

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

omit [TopologicalSpace F] in
/-- Every actual unequal-rank block lies in the large mirabolic subgroup. -/
theorem block_last_row (j k : ℕ) (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F)
    (a : Fin (n + (j + k + 1) + 1)) :
    (unequalRankMatrix j k g x).val (Fin.last (n + (j + k + 1))) a =
      if a = Fin.last (n + (j + k + 1)) then 1 else 0 := by
  rw [unequalRankMatrix_val]
  have hrow : ¬ ((Fin.last (n + (j + k + 1))).val < n + 1) := by
    simp only [Fin.val_last]
    omega
  have hrect : ¬ (n + 1 ≤ (Fin.last (n + (j + k + 1))).val ∧
      (Fin.last (n + (j + k + 1))).val < n + 1 + j) := by
    simp only [Fin.val_last]
    omega
  simp only [Matrix.add_apply, appendIdentity_entry, dite_eq_right hrow,
    rectangularEntries, dite_eq_right hrect, add_zero]
  simp only [eq_comm]

/-- Agreement on mirabolic matrices gives equality of the actual integrands. -/
theorem integrand_eq_of_mirabolic_eq (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (j k : ℕ)
    (f φ : WhittakerFunctions ψ (n + (j + k + 1)))
    (f' : InverseWhittakerFunctions ψ n)
    (h : ∀ q : Langlands.GeneralLinear (n + (j + k + 1) + 1) F,
      (∀ a, q.val (Fin.last (n + (j + k + 1))) a =
        if a = Fin.last (n + (j + k + 1)) then 1 else 0) → f.val q = φ.val q)
    (s : ℂ) :
    unequalRankIntegrand ψ abv j k f f' s =
      unequalRankIntegrand ψ abv j k φ f' s := by
  funext x q
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk, h _ (block_last_row j k g x)]

/-- Mirabolic agreement also preserves the required product integrability. -/
theorem converges_iff_of_mirabolic_eq (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (f φ : WhittakerFunctions ψ (n + (j + k + 1)))
    (f' : InverseWhittakerFunctions ψ n)
    (h : ∀ q : Langlands.GeneralLinear (n + (j + k + 1) + 1) F,
      (∀ a, q.val (Fin.last (n + (j + k + 1))) a =
        if a = Fin.last (n + (j + k + 1)) then 1 else 0) → f.val q = φ.val q)
    (s : ℂ) :
    UnequalRankConverges ψ abv j k μ ν f f' s ↔
      UnequalRankConverges ψ abv j k μ ν φ f' s := by
  unfold UnequalRankConverges
  rw [integrand_eq_of_mirabolic_eq ψ abv j k f φ f' h s]

/-- Agreement on mirabolic matrices gives agreement of the nested block integrals.
This pointwise comparison needs no integrability assumption. -/
theorem integral_eq_of_mirabolic_eq (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (f φ : WhittakerFunctions ψ (n + (j + k + 1)))
    (f' : InverseWhittakerFunctions ψ n)
    (h : ∀ q : Langlands.GeneralLinear (n + (j + k + 1) + 1) F,
      (∀ a, q.val (Fin.last (n + (j + k + 1))) a =
        if a = Fin.last (n + (j + k + 1)) then 1 else 0) → f.val q = φ.val q)
    (s : ℂ) :
    unequalRankIntegral ψ abv j k μ ν f f' s =
      unequalRankIntegral ψ abv j k μ ν φ f' s := by
  unfold unequalRankIntegral
  rw [integrand_eq_of_mirabolic_eq ψ abv j k f φ f' h s]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A unit test integral in the actual coefficient models supplies unit membership
in their Laurent span, without requiring rationality of the other integrals. -/
theorem one_mem_of_unit_integral (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (h : ∀ s : ℂ, unequalRankModelIntegral ψ abv j k μ ν π σ ℓ ℓ' f f' s = 1) :
    (1 : RationalFunctions) ∈ zetaSpan
      (unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ') := by
  apply Submodule.subset_span
  refine ⟨f, f', 0, ?_⟩
  intro s _
  simp [h s, RatFunc.denom_one, RatFunc.eval_one]

/-- Once a compact test has a unit integral and an actual coefficient lift,
their pointwise agreement supplies the requested Laurent-span membership. -/
theorem one_mem_of_mirabolic_unit_integral (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ (n + (j + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (φ : WhittakerFunctions ψ (n + (j + k + 1)))
    (hlift : ∀ g : Langlands.GeneralLinear (n + (j + k + 1) + 1) F,
      (∀ a, g.val (Fin.last (n + (j + k + 1))) a =
        if a = Fin.last (n + (j + k + 1)) then 1 else 0) → f.val.val g = φ.val g)
    (hunit : ∀ s : ℂ, unequalRankIntegral ψ abv j k μ ν φ f'.val s = 1) :
    (1 : RationalFunctions) ∈ zetaSpan
      (unequalRankRationalValues j k q ψ abv μ ν π σ ℓ ℓ') := by
  apply one_mem_of_unit_integral q ψ abv j k μ ν π σ ℓ ℓ' f f'
  intro s
  change unequalRankIntegral ψ abv j k μ ν f.val f'.val s = 1
  rw [integral_eq_of_mirabolic_eq ψ abv j k μ ν f.val φ f'.val hlift s, hunit s]

end Langlands.RankinSelberg.UnitSpanAssembly

namespace Langlands.RankinSelberg.UnitSpanAssembly

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

/-- Assemble the compact test and its actual coefficient lift using the exact interfaces. -/
theorem unitSpan_of_kirillov_and_compact_test {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ)
    (hKirillov : Langlands.WhittakerTypeKirillovStatement.{uF, uV})
    (hTest : UnequalRankMirabolicUnitTestStatement.{uF, uW} F T n j k) :
    UnequalRankUnitSpanStatement.{uF, uV, uW} F T n j k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ hright μ hμ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨φ, f', hφ, hunit⟩ := hTest ψ μ hμ ν W σ hσ ℓ' hℓ'
  obtain ⟨f, hlift⟩ := Whittaker.modelKirillovTransfer.{uF, uV}
    hKirillov p inferInstance F T (n + (j + k + 1)) V π ψ hπ ℓ hℓ φ hφ
  exact one_mem_of_mirabolic_unit_integral T.residueCardinality ψ
    (normalizedAbsoluteValue T) j k μ (rectangularMeasure ν j (n + 1))
    π σ ℓ ℓ' f f' φ hlift (fun s => (hunit s).2)

/-- Use canonical Kirillov to lift a supplied compact test into the specified model. -/
theorem unitSpan_of_compact_test {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ)
    (hTest : UnequalRankMirabolicUnitTestStatement.{uF, uW} F T n j k) :
    UnequalRankUnitSpanStatement.{uF, uV, uW} F T n j k :=
  unitSpan_of_kirillov_and_compact_test F T n j k
    Langlands.whittakerTypeKirillov.{uF, uV} hTest

end Langlands.RankinSelberg.UnitSpanAssembly

namespace Langlands.RankinSelberg

/-- Every actual unequal-rank JPSS zeta span contains one. -/
theorem unequalRankUnitSpan.{uF, uV, uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ) :
    UnequalRankUnitSpanStatement.{uF, uV, uW} F T n j k :=
  UnitSpanAssembly.unitSpan_of_compact_test F T n j k
    (unequalRankMirabolicUnitTest.{uF, uW} F T n j k)

end Langlands.RankinSelberg
