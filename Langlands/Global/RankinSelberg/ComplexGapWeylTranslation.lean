import Langlands.Analysis.SchwartzMatrixNorm
import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial
import Langlands.Global.RankinSelberg.ComplexUnequalDualFamily
import Langlands.Global.RankinSelberg.UnfoldingWeylCompact

/-! # The Weyl translate of a complex Godement test -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped Matrix Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapWeylTranslation

open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry operatorToEntry_apply)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)
open Langlands.GeneralLinear (determinant permutation)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementGaussianPolynomial
  (Coordinates coordinates coordinatePartCLM gaussianPolynomial gaussianPolynomial_apply matrixGaussian matrixSqNorm)
open ComplexUnequalFamily (unfoldingWeyl_mem_unitary)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable

variable {r t : ℕ}

local notation "N" => (r + 1 + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ

private theorem weyl_eq_permutation (h : t < r + 1) :
    ArchimedeanLocal.unfoldingWeyl (K := ℂ) h = permutation N ℂ (unfoldingWeylPermutation h) := by
  simp only [ArchimedeanLocal.unfoldingWeyl, unfoldingWeylPermutation, Langlands.GeneralLinear.weylLong]
  rw [show (1 : Langlands.GeneralLinear (t + 1) ℂ) =
    permutation (t + 1) ℂ (Equiv.refl _) from (map_one _).symm,
    blockSum_permutation, reindex_permutation]

private theorem right_weyl_apply (h : t < r + 1) (X : Rect) (i : Fin (r + 1)) (j : Fin N) :
    (X * (ArchimedeanLocal.unfoldingWeyl (K := ℂ) h).val) i j = X i (unfoldingWeylPermutation h j) := by
  rw [weyl_eq_permutation h]
  change (X * (((unfoldingWeylPermutation h)⁻¹).toPEquiv.toMatrix : Matrix (Fin N) (Fin N) ℂ))
    i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem abs_det_weyl (h : t < r + 1) :
    complexNormalizedAbs (ArchimedeanLocal.unfoldingWeyl (K := ℂ) h).val.det = 1 := by
  have hd := normSqC_det_unitary ⟨_, unfoldingWeyl_mem_unitary h⟩
  exact_mod_cast (show ((complexNormalizedAbs
    (ArchimedeanLocal.unfoldingWeyl (K := ℂ) h).val.det : ℝ) : ℂ) = 1 from hd)

/-- Right translating the continued value by the unfolding Weyl element
translates its rectangular test and multiplies by the adjoining character. -/
theorem continuedValue_mul_weyl (h : t < r + 1) (ν : Measure G) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (W : G → ℂ) (g : G') (s : ℂ) :
    continuedValue ν μ d a Φ W (g * ArchimedeanLocal.unfoldingWeyl h) s =
      (d.character (determinant (ArchimedeanLocal.unfoldingWeyl (K := ℂ) h)) : ℂ) *
        continuedValue ν μ d a (rightTest (ArchimedeanLocal.unfoldingWeyl h) Φ) W g s := by
  let w := ArchimedeanLocal.unfoldingWeyl (K := ℂ) h
  have hTest : rightTest (g * w) Φ = rightTest g (rightTest w Φ) := by
    ext X
    simp only [rightTest_apply, Units.val_mul, Matrix.mul_assoc]
  have hWeight (z : ℂ) : characterWeight d z (determinant w) = (d.character (determinant w) : ℂ) := by
    change (d.character (determinant w) : ℂ) * ((complexNormalizedAbs w.val.det : ℝ) : ℂ) ^ z = _
    rw [abs_det_weyl h, Complex.ofReal_one, Complex.one_cpow, mul_one]
  have hAbs : complexNormalizedAbs (g * w).val.det = complexNormalizedAbs g.val.det := by
    simp only [Units.val_mul, Matrix.det_mul, complexNormalizedAbs, norm_mul, mul_pow]
    rw [show ‖w.val.det‖ ^ 2 = 1 from abs_det_weyl h, mul_one]
  have hPower : ArchimedeanLocal.detPower complexNormalizedAbs (g * w) s =
      ArchimedeanLocal.detPower complexNormalizedAbs g s := by
    simp only [ArchimedeanLocal.detPower, hAbs]
  change continuedValue ν μ d a Φ W (g * w) s = _
  simp only [continuedValue, hTest, hPower, map_mul determinant, map_mul (characterWeight d _),
    hWeight]
  ring

/-- The coordinate renaming on a Gaussian polynomial induced by the tail Weyl permutation. -/
def weylCoordinate (h : t < r + 1) (v : Coordinates (r + 1) N) : Coordinates (r + 1) N :=
  (v.1, unfoldingWeylPermutation h v.2.1, v.2.2)

variable (r t) in
/-- The Weyl-translated Gaussian monomial has the same coefficient and
the permuted coordinate exponents. -/
def ComplexGapWeylTranslationStatement : Prop :=
  ∀ (h : t < r + 1) (b : Coordinates (r + 1) N →₀ ℕ) (c : ℂ),
    rightTest (ArchimedeanLocal.unfoldingWeyl h) (operatorToEntry (gaussianPolynomial (monomial b c))) =
      operatorToEntry (gaussianPolynomial (monomial (b.mapDomain (weylCoordinate h)) c))

theorem complexGapWeylTranslation : ComplexGapWeylTranslationStatement r t := by
  intro h b c
  let w := ArchimedeanLocal.unfoldingWeyl (K := ℂ) h
  have hGaussian (X : Rect) : matrixGaussian (X * w.val) = matrixGaussian X := by
    unfold matrixGaussian matrixSqNorm
    congr 2
    apply congrArg Neg.neg
    refine Finset.sum_congr rfl fun i _ => ?_
    calc
      _ = ∑ j, ‖X i (unfoldingWeylPermutation h j)‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ =>
          congrArg (fun z : ℂ => ‖z‖ ^ 2) (right_weyl_apply h X i j)
      _ = _ := Equiv.sum_comp (unfoldingWeylPermutation h) (fun j => ‖X i j‖ ^ 2)
  have hCoordinates (X : Rect) : coordinates (X * w.val) = coordinates X ∘ weylCoordinate h := by
    funext v
    exact congrArg (coordinatePartCLM v.2.2) (right_weyl_apply h X v.1 v.2.1)
  ext X
  simp only [rightTest_apply, operatorToEntry_apply, gaussianPolynomial_apply]
  rw [hGaussian, hCoordinates, ← eval_rename, rename_monomial]

end Langlands.Global.RankinSelbergGlobal.ComplexGapWeylTranslation
