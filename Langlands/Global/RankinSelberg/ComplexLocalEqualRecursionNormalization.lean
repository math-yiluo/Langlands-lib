import Langlands.Global.RankinSelberg.ComplexLocalEqualUnfolding
import Langlands.Global.RankinSelberg.ComplexLocalUnipotentBlockMeasure

/-! # Common Haar normalization of the two equal-rank recursions -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis (rectangularJoin)
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped NNReal ENNReal

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
local notation "NH" => Langlands.GeneralLinear.upperUnipotent m ℂ
local notation "NG" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Col" => Fin m → ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

private def columnMeasure (a : ℂˣ) : Measure Col :=
  Measure.pi (fun _ : Fin m => (complexSelfDualMeasure a).measure)

local notation "μz[" a "]" => columnMeasure (r := r) a

/-- The last-column and smaller-unipotent kernel of one rectangle integral. -/
def complexEqualRectangleKernel (a : ℂˣ) (f : Rect → ℂ) (p : NH × Col) : ℂ :=
  f (rectangularJoin p.1.val.val p.2) *
    (complexWhittakerCharacter a p.1.val * (complexScaledCharacter a).complex (p.2 (Fin.last r)))

private theorem unipotentRectangleIntegral (D : ComplexQuotientMeasureData (r + 1))
    (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ) :
    ∃ c : ℝ≥0, 0 < c ∧
    ∀ (b : ℂˣ), complexSelfDualMeasure b = complexSelfDualMeasure a →
    ∀ (f : Rect → ℂ), Integrable (complexEqualRectangleKernel b f) (D₁.unipotentHaar.prod μz[b]) →
      (∫ u : NG, f (complexSquareFirstRows u.val.val) *
        complexWhittakerCharacter b u.val ∂D.unipotentHaar) =
        (c : ℂ) * ∫ u : NH, ∫ z : Col, complexEqualRectangleKernel b f (u, z)
          ∂μz[b] ∂D₁.unipotentHaar := by
  obtain ⟨c, hc, hμ⟩ := complexLocalUnipotentBlockMeasure m a
    D₁.unipotentHaar D.unipotentHaar D₁.unipotentHaar_isHaar D.unipotentHaar_isHaar
  refine ⟨c, hc, ?_⟩
  intro b hba f hf
  let e := complexUnipotentBlockJoin m
  let I (u : NG) := f (complexSquareFirstRows u.val.val) * complexWhittakerCharacter b u.val
  have hI : I ∘ e = complexEqualRectangleKernel b f := by
    funext p
    rcases p with ⟨u, z⟩
    change f (complexSquareFirstRows (e (u, z)).val.val) *
      complexWhittakerCharacter b (e (u, z)).val = _
    rw [show complexSquareFirstRows (e (u, z)).val.val = rectangularJoin u.val.val z from
      complexUnipotentBlockJoin_rectangle u z, complexWhittakerCharacter_blockJoin]
    rfl
  have hμb : D.unipotentHaar = c • (D₁.unipotentHaar.prod μz[b]).map e := by
    simpa only [columnMeasure, hba] using hμ
  let eH := upperEntryCoordinates m (K := ℂ)
  let : LocallyCompactSpace NH := eH.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology NH := eH.secondCountableTopology
  let : D₁.unipotentHaar.IsHaarMeasure := D₁.unipotentHaar_isHaar
  let : (complexSelfDualMeasure b).measure.IsAddHaarMeasure := (complexSelfDualMeasure b).isAddHaar
  let : SFinite μz[b] := by unfold columnMeasure; infer_instance
  change (∫ u, I u ∂D.unipotentHaar) = _
  rw [hμb, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map]
  change c • (∫ p, (I ∘ e) p ∂D₁.unipotentHaar.prod μz[b]) = _
  rw [hI, integral_prod _ hf, NNReal.smul_def, Complex.real_smul]

private theorem squareFirstRows_mul (X Y : Matrix (Fin n) (Fin n) ℂ) :
    complexSquareFirstRows (X * Y) = complexSquareFirstRows X * Y := by
  ext i j
  rfl

variable (r) in
/-- One positive scalar compares the full unipotent recursion to the
rectangle recursion for both signs of the additive character. -/
def ComplexLocalEqualRecursionNormalizationStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ),
  ∃ c : ℝ≥0, 0 < c ∧
  ∀ (b : ℂˣ), complexSelfDualMeasure b = complexSelfDualMeasure a →
  ∀ (η : ℂˣ →* ℂˣ) (Φ : Rect → ℂ) (U : H → ℂ) (g : G),
    (∀ k : H, Integrable
      (complexEqualRectangleKernel (-b) (fun X => Φ ((k⁻¹).val * X * g.val)))
      (D₁.unipotentHaar.prod μz[-b])) →
    complexEqualUnipotentRecursion D D₁ η b Φ U g =
      (c : ℂ) * ((η (determinant g) : ℂ) * P g ((m : ℕ) / 2) *
        ∫ q : Q, (∫ u : NH, ∫ z : Col,
          complexEqualRectangleKernel (-b) (fun X => Φ ((q.out⁻¹).val * X * g.val)) (u, z)
          ∂μz[-b] ∂D₁.unipotentHaar) *
          U q.out * (η (determinant q.out⁻¹) : ℂ) * P q.out⁻¹ ((n : ℕ) / 2) ∂D₁.measure)

theorem complexLocalEqualRecursionNormalization : ComplexLocalEqualRecursionNormalizationStatement r := by
  intro D D₁ a
  obtain ⟨c, hc, hFiber⟩ := unipotentRectangleIntegral D D₁ a
  refine ⟨c, hc, ?_⟩
  intro b hba η Φ U g hf
  have hneg : complexSelfDualMeasure (-b) = complexSelfDualMeasure a :=
    (selfDualMeasure_neg b).trans hba
  have hfiber (k : H) :
      (∫ u : NG, Φ ((k⁻¹).val * complexSquareFirstRows (u.val * g).val) *
        complexWhittakerCharacter (-b) u.val ∂D.unipotentHaar) =
      (c : ℂ) * ∫ u : NH, ∫ z : Col,
        complexEqualRectangleKernel (-b) (fun X => Φ ((k⁻¹).val * X * g.val)) (u, z)
        ∂μz[-b] ∂D₁.unipotentHaar := by
    simp only [Units.val_mul, squareFirstRows_mul, ← Matrix.mul_assoc]
    exact hFiber (-b) hneg (fun X => Φ ((k⁻¹).val * X * g.val)) (hf k)
  change (η (determinant g) : ℂ) * P g ((m : ℕ) / 2) *
    (∫ q : Q, (∫ u : NG, Φ ((q.out⁻¹).val * complexSquareFirstRows (u.val * g).val) *
      complexWhittakerCharacter (-b) u.val ∂D.unipotentHaar) *
        U q.out * (η (determinant q.out⁻¹) : ℂ) * P q.out⁻¹ ((n : ℕ) / 2) ∂D₁.measure) = _
  simp only [hfiber, mul_assoc, integral_const_mul]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
