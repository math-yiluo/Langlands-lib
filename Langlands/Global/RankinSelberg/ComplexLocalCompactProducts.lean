import Langlands.Global.RankinSelberg.ComplexLocalCompactInsertionIntegrability
import Langlands.Global.RankinSelberg.ComplexLocalEqualUnfoldedSign
import Langlands.Global.RankinSelberg.ComplexLocalAdjacentUnfolding

/-! # The quotient factors in Jacquet's compact expansions -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped Langlands.Archimedean.ComplexDuality Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Kg" => unitaryCompact ℂ n
local notation "Kh" => unitaryCompact ℂ m
local notation "MatG" => Matrix (Fin n) (Fin n) ℂ
local notation "MatH" => Matrix (Fin m) (Fin m) ℂ
local notation "pad" => (padGL (R := ℂ) (Nat.le_succ (r + 1)))
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "gap" => Nat.lt_succ_self r

private theorem equalUnfoldedInner_eq_unequal (U : H → ℂ) (V : G → ℂ) (s : ℂ) (q : Q) :
    complexEqualUnfoldedInner U V 1 s q = complexUnequalIntegrand gap V U s q := by
  have hshift : (r + 1 - r : ℕ) = 1 := by omega
  simp only [complexEqualUnfoldedInner, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    hshift, Nat.cast_one, mul_one]
  rw [mul_comm (U q.out)]

/-- In the equal-rank unfolding the compact projection expansion produces
the actual smaller corank-one zeta integrals as the quotient factors. -/
theorem complexEqualUnfoldedIntegral_eq_sum_products
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (ν : Measure Kg) [SFinite ν] (i : Kg →* Kg) (hi : Measurable i)
    (κ : Kg → ℂ) (η : ℂˣ →* ℂˣ) (Φ : MatG → ℂ)
    (U : H → ℂ) (V : G → ℂ) (s : ℂ)
    (hΦ : ∀ X, ∫ k, κ k * complexCompactMatrixTranslate (η.comp invMonoidHom) Φ (i k) X ∂ν = Φ X)
    {d : ℕ} (Vj : Fin d → G → ℂ) (bj : Fin d → G → ℂ)
    (hExp : ∀ x g, (∫ k, κ k * V (x * (i k).val * g) ∂ν) = ∑ j, Vj j x * bj j g) :
    let A := complexWeightedMatrixTest η Φ (s + ((m : ℕ) : ℂ) / 2)
    let F := fun (q : Q) (g : G) => complexEqualUnfoldedInner U V g s q
    Integrable (fun p : Q × G => A p.2 * F p.1 p.2) (D.measure.prod μ) →
    (∀ᵐ q ∂D.measure, Integrable
      (fun p : Kg × G => κ p.1 * A ((i p.1).val⁻¹ * p.2) * F q p.2) (ν.prod μ)) →
    (∀ j, Integrable (complexUnequalIntegrand gap (Vj j) U s) D.measure) →
    (∀ j, Integrable (fun g => A g * bj j g) μ) →
    complexEqualUnfoldedIntegral μ D η Φ U V s =
      ∑ j, complexUnequalIntegral gap D (Vj j) U s * (∫ g, A g * bj j g ∂μ) := by
  intro A F hProd hInt hUn hMat
  refine complexLocalCompactIntegralExpansion Q D.measure ν μ i hi η Φ κ
    (s + ((m : ℕ) : ℂ) / 2) F hΦ hProd hInt d
    (fun j => complexUnequalIntegrand gap (Vj j) U s) bj ?_ hUn hMat
  intro q g
  let b := U q.out * P q.out (s - 1 / 2)
  have hF (k : Kg) : κ k * F q ((i k).val * g) = b * (κ k * V (pad q.out * (i k).val * g)) := by
    simp only [F, b, complexEqualUnfoldedInner, mul_assoc]
    ring
  simp_rw [hF]
  rw [integral_const_mul, hExp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← equalUnfoldedInner_eq_unequal]
  simp only [complexEqualUnfoldedInner, mul_one, b]
  ring

/-- In the corank-one unfolding the compact projection expansion produces
the actual smaller equal-rank zeta integrals as the quotient factors. -/
theorem complexAdjacentUnfoldedIntegral_eq_sum_products
    (D : ComplexQuotientMeasureData r) [SFinite D.measure] [SFinite D.groupHaar]
    (ν : Measure Kh) [SFinite ν] (i : Kh →* Kh) (hi : Measurable i)
    (κ : Kh → ℂ) (η : ℂˣ →* ℂˣ) (Φ : MatH → ℂ) (φ : (Fin m → ℂ) → ℂ)
    (U V : H → ℂ) (s : ℂ)
    (hΦ : ∀ X, ∫ k, κ k * complexCompactMatrixTranslate (η.comp invMonoidHom) Φ (i k) X ∂ν = Φ X)
    {d : ℕ} (Vj : Fin d → H → ℂ) (bj : Fin d → H → ℂ)
    (hExp : ∀ x g, (∫ k, κ k * V (x * (i k).val * g) ∂ν) = ∑ j, Vj j x * bj j g) :
    let A := complexWeightedMatrixTest η Φ (s + (r : ℂ) / 2)
    let F := fun (q : Q) (g : H) => complexEqualIntegrand U (fun x => V (x * g)) φ s q
    Integrable (fun p : Q × H => A p.2 * F p.1 p.2) (D.measure.prod D.groupHaar) →
    (∀ᵐ q ∂D.measure, Integrable
      (fun p : Kh × H => κ p.1 * A ((i p.1).val⁻¹ * p.2) * F q p.2) (ν.prod D.groupHaar)) →
    (∀ j, Integrable (complexEqualIntegrand U (Vj j) φ s) D.measure) →
    (∀ j, Integrable (fun g => A g * bj j g) D.groupHaar) →
    complexAdjacentUnfoldedIntegral D η Φ φ U V s =
      ∑ j, complexEqualIntegral D U (Vj j) φ s * (∫ g, A g * bj j g ∂D.groupHaar) := by
  intro A F hProd hInt hEqInt hMat
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  calc
    _ = ∫ g, A g * (∫ q, F q g ∂D.measure) ∂D.groupHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => mul_comm
        (complexEqualIntegral D U (fun x => V (x * g)) φ s)
        (complexAdjacentMatrixWeight η Φ s g)
    _ = _ := by
      refine complexLocalCompactIntegralExpansion Q D.measure ν D.groupHaar i hi η Φ κ
        (s + (r : ℂ) / 2) F hΦ hProd hInt d
        (fun j => complexEqualIntegrand U (Vj j) φ s) bj ?_ hEqInt hMat
      intro q g
      let b := U q.out * φ (RankinSelberg.lastRow q.out) * P q.out s
      have hF (k : Kh) : κ k * F q ((i k).val * g) = b * (κ k * V (q.out * (i k).val * g)) := by
        simp only [F, b, complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, mul_assoc]
        ring
      simp_rw [hF]
      rw [integral_const_mul, hExp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, b]
      ring

private theorem shifted_re (s : ℂ) (t : ℝ) : (s + (t : ℂ)).re = s.re + t := by
  simp only [Complex.add_re, Complex.ofReal_re]

/-- Compact insertion is absolutely integrable for every quotient representative in
the equal-rank expansion, with a single half-plane. -/
def ComplexLocalEqualCompactInsertionStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] (ν : Measure Kg) [IsFiniteMeasure ν]
    (i : Kg →* Kg), Continuous i →
  ∀ (κ : Kg → ℂ), Continuous κ →
  ∀ (d : ComplexCharacterData) (Φ : 𝓢(MatG, ℂ)) (U : H → ℂ)
    (es : List ComplexCharacterData) (a : ℂˣ) (V : complexWhittakerModel (r + 1) es a),
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ q : Q,
      let A := complexWeightedMatrixTest d.character Φ (s + ((m : ℕ) : ℂ) / 2)
      Integrable (fun p : Kg × G =>
        κ p.1 * A ((i p.1).val⁻¹ * p.2) * complexEqualUnfoldedInner U V.val p.2 s q)
        (ν.prod μ)

theorem complexLocalEqualCompactInsertion : ComplexLocalEqualCompactInsertionStatement (r := r) := by
  intro μ _ _ ν _ i hi κ hκ d Φ U es a V
  obtain ⟨τ, hτ⟩ := complexLocalCompactInsertionIntegrability μ ν i hi κ hκ d Φ es a V
  let t := (m : ℝ) / 2
  refine ⟨τ - t, fun s hs q => ?_⟩
  have ht : (t : ℂ) = ((m : ℕ) : ℂ) / 2 := by simp [t]
  have hs' : τ < (s + (t : ℂ)).re := by rw [shifted_re]; linarith
  rw [← ht]
  refine ((hτ (s + (t : ℂ)) hs' (pad q.out)).mul_const
    (U q.out * P q.out (s - 1 / 2))).congr (ae_of_all _ fun p => ?_)
  simp only [complexEqualUnfoldedInner]
  ac_rfl

/-- Compact insertion is absolutely integrable for every quotient representative in
the corank-one expansion, with a single half-plane. -/
def ComplexLocalAdjacentCompactInsertionStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.groupHaar]
    (ν : Measure Kh) [IsFiniteMeasure ν] (i : Kh →* Kh), Continuous i →
  ∀ (κ : Kh → ℂ), Continuous κ →
  ∀ (d : ComplexCharacterData) (Φ : 𝓢(MatH, ℂ)) (φ : 𝓢(Fin m → ℂ, ℂ)) (U : H → ℂ)
    (es : List ComplexCharacterData) (a : ℂˣ) (V : complexWhittakerModel r es a),
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ q : Q,
      let A := complexWeightedMatrixTest d.character Φ (s + (r : ℂ) / 2)
      Integrable (fun p : Kh × H =>
        κ p.1 * A ((i p.1).val⁻¹ * p.2) *
          complexEqualIntegrand U (fun x => V.val (x * p.2)) φ s q)
        (ν.prod D.groupHaar)

theorem complexLocalAdjacentCompactInsertion :
    ComplexLocalAdjacentCompactInsertionStatement (r := r) := by
  intro D _ ν _ i hi κ hκ d Φ φ U es a V
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  obtain ⟨τ, hτ⟩ := complexLocalCompactInsertionIntegrability D.groupHaar ν i hi κ hκ d Φ es a V
  let t := (r : ℝ) / 2
  refine ⟨τ - t, fun s hs q => ?_⟩
  have ht : (t : ℂ) = (r : ℂ) / 2 := by simp [t]
  have hs' : τ < (s + (t : ℂ)).re := by rw [shifted_re]; linarith
  rw [← ht]
  refine ((hτ (s + (t : ℂ)) hs' q.out).mul_const
    (U q.out * φ (RankinSelberg.lastRow q.out) * P q.out s)).congr (ae_of_all _ fun p => ?_)
  simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand]
  ac_rfl

/-- Fixed-quotient-variable convergence for both compact integral comparisons. -/
def ComplexLocalCompactProductsStatement : Prop :=
  ComplexLocalEqualCompactInsertionStatement (r := r) ∧
    ComplexLocalAdjacentCompactInsertionStatement (r := r)

theorem complexLocalCompactProducts : ComplexLocalCompactProductsStatement (r := r) :=
  ⟨complexLocalEqualCompactInsertion, complexLocalAdjacentCompactInsertion⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
