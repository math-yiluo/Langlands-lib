import Langlands.Global.RankinSelberg.ComplexEqualSquarePolynomialFamily
import Langlands.Global.RankinSelberg.ComplexGodementStandardGaussians
import Langlands.Global.RankinSelberg.ComplexLocalEqualChamberUnfolding
import Langlands.Global.RankinSelberg.ComplexLocalEqualNormalizedFactors
import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz

/-! # Polynomial traces of standard Gaussian equal-rank recursion tests -/

noncomputable section

open MeasureTheory MvPolynomial
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GodementJacquet
open Langlands.LocalFactor.Archimedean
open ComplexEqualPolynomialGeneration (IsGaussianPolynomialRow)
open ComplexGodement (shiftedCharacter)
open ComplexGodementGaussianPolynomial (Coordinates coordinates matrixSqNorm standardMatrixTest
  standardMatrixTest_apply scalePolynomial)
open ComplexSquareZeta (squarePolynomialGaussian)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable {m : ℕ}
local notation "n" => m + 1
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "scale" => (2 * Real.pi : ℝ)

/-- The product of a standard rectangular test and a standard Gaussian row is a square
polynomial Gaussian of the same scale. -/
theorem standardSquareProduct_polynomialGaussian (p : MvPolynomial (Coordinates m n) ℂ)
    (φ : 𝓢(Row, ℂ)) (hφ : IsGaussianPolynomialRow scale φ) :
    ∃ P : MvPolynomial (Coordinates n n) ℂ,
      complexSquareProductTest (operatorToEntry (standardMatrixTest p)) φ = squarePolynomialGaussian P := by
  obtain ⟨q, hq⟩ := hφ
  let leading (j : Coordinates m n) : Coordinates n n := (j.1.castSucc, j.2)
  let last (j : Fin n × Bool) : Coordinates n n := (Fin.last m, j.1, j.2)
  refine ⟨rename leading (scalePolynomial p) * rename last q, funext fun X => ?_⟩
  let Y := complexSquareFirstRows X
  let v := X (Fin.last m)
  have hsq : matrixSqNorm X = matrixSqNorm Y + ∑ j, ‖v j‖ ^ 2 := by
    rw [matrixSqNorm, Fin.sum_univ_castSucc]
    rfl
  have hLead : coordinates X ∘ leading = coordinates Y := rfl
  let c (j : Fin n × Bool) : ℂ := if j.2 then (v j.1).im else (v j.1).re
  have hLast : coordinates X ∘ last = c := by
    funext j
    obtain ⟨i, b⟩ := j
    cases b <;> rfl
  have hRow : φ v = eval c q * (Real.exp (-scale * ∑ j, ‖v j‖ ^ 2) : ℂ) := hq v
  have hA : (operatorToEntry (standardMatrixTest p)) Y = eval (coordinates Y) (scalePolynomial p) *
      (Real.exp (-scale * matrixSqNorm Y) : ℂ) := standardMatrixTest_apply p Y
  change (operatorToEntry (standardMatrixTest p)) Y * φ v = _
  rw [hA, hRow, squarePolynomialGaussian, map_mul, eval_rename, eval_rename, hLead, hLast]
  change _ = _ * (Real.exp (-scale * matrixSqNorm X) : ℂ)
  rw [hsq, mul_add, Real.exp_add, Complex.ofReal_mul]
  ring

variable {r : ℕ}

local notation "k" => r + 1
local notation "N" => r + 1 + 1
local notation "G" => Langlands.GeneralLinear N ℂ

/-- With polynomial adjacent normalizations, each standard Gaussian recursion test has a
polynomial equal-rank trace in the positive adjoining-exponent chamber. -/
def ComplexEqualGaussianChamberStatement : Prop :=
  ∀ (a : ℂˣ), ComplexAdjacentPolynomialAtRank r (-a) →
    ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
      (d : ComplexCharacterData) (ds : List ComplexCharacterData), ds.length = k →
    ∀ (e : Fin N → ComplexCharacterData) (U : complexWhittakerModel r ds a)
      (B : complexStandardKFinite N (List.ofFn e) →ₗ[ℂ] (G → ℂ)),
      IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-a) B →
    ∀ (f : complexStandardKFinite N (List.ofFn e)) (p : MvPolynomial (Coordinates k N) ℂ)
      (φ : 𝓢(Fin N → ℂ, ℂ)), IsGaussianPolynomialRow scale φ →
      ∃ (P : ℂ → Polynomial ℂ) (τ σ : ℝ), ∀ z s : ℂ, τ < z.re → σ < s.re →
        (P z).eval s = (complexPairLFactor (shiftedCharacter d z :: ds) (List.ofFn e)).denominator s *
          complexEqualIntegral D
            (complexJacquetRecursion a D₁ (operatorToEntry (standardMatrixTest p)) U.val
              (shiftedCharacter d z).character.toMonoidHom) (B f) φ s

set_option maxHeartbeats 900000 in
theorem complexEqualGaussianChamber : ComplexEqualGaussianChamberStatement (r := r) := by
  intro a hAdj D D₁ d ds hds e U B hB f p φ hφ
  let es := List.ofFn e
  let Φ := operatorToEntry (standardMatrixTest p)
  let V : complexWhittakerModel (r + 1) es (-a) :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  obtain ⟨q, hq⟩ := standardSquareProduct_polynomialGaussian p φ hφ
  let Ψ := complexMatrixEntryToOperator (complexSquareProductSchwartz Φ φ)
  have hΨ : (Ψ : Matrix (Fin N) (Fin N) ℂ → ℂ) = complexSquareProductTest Φ φ :=
    funext (complexSquareProductSchwartz_apply Φ φ)
  obtain ⟨A, τ, σ, hA⟩ := complexEqualSquarePolynomialFamily a hAdj D D₁ d ds hds e U B hB f Ψ q (hΨ.trans hq)
  open scoped Matrix.Norms.Elementwise in
  obtain ⟨Φd, hΦd⟩ := exists_schwartz_complexRectangularFourier (-a) Φ
  obtain ⟨φd, hφd⟩ := exists_schwartz_complexFourierTransform a φ
  obtain ⟨c, hc, hUnfold⟩ := complexLocalEqualChamberUnfolding (r := r) D D₁ a
  obtain ⟨τ', σ', hU⟩ := (hUnfold d ds es hds List.length_ofFn U V Φ Φd φ φd hΦd hφd).1
  have hc₀ : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨fun z => Polynomial.C (c : ℂ)⁻¹ * A z, max τ τ', max σ σ', fun z s hz hs => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_C, hA z s ((le_max_left _ _).trans_lt hz)
    ((le_max_left _ _).trans_lt hs), equalDoubleDenominator_eq_pair, hΨ]
  have he := hU z s ((le_max_right _ _).trans_lt hz) ((le_max_right _ _).trans_lt hs)
  change (c : ℂ) * complexEqualIntegral D _ (B f) φ s = _ at he
  rw [← he, mul_left_comm ((c : ℂ)⁻¹), ← mul_assoc (c : ℂ)⁻¹ (c : ℂ), inv_mul_cancel₀ hc₀, one_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
