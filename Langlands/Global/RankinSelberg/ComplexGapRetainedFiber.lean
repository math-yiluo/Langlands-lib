import Langlands.Global.RankinSelberg.ComplexGapSquareWeighted
import Langlands.Global.RankinSelberg.ComplexUnequalMellinReduction

/-! # Normalization of the two integrals at a fixed retained matrix -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar matrixLebesgue)
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open Langlands.GodementJacquet (complexMatrixHaar_measurePreserving_inverseTranspose inverseTransposeMeasurableEquiv)
open ComplexAdjacentUnfolding (splitSquareTransform)
open ComplexGapSquareAverage (squareKernel)
open ComplexUnequalMellinReduction (sigmaFinite_quotient)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction

variable {r t : ℕ} (h : t < r)
local notation "H" => G (t + 1)
local notation "Mat" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ
local notation "X" => Q t × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
local notation "ι" => inverseTranspose (t + 1) ℂ
local notation "ν" => complexGeneralLinearHaar (t + 1)

/-- The ordinary separated kernel with the retained coefficient omitted. -/
def ordinaryFiber (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ))
    (W : G (r + 1) → ℂ) (V : H → ℂ) (s : ℂ) (p : Q t × H) : ℂ :=
  complexUnequalIntegrand h W (ρ p.2 V) s p.1 * squareKernel d Φ (fun _ => 1) s p.2

/-- The reflected separated kernel with the retained coefficient and Weyl sign omitted. -/
def reflectedFiber (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ))
    (W : G (r + 1) → ℂ) (V : H → ℂ) (s : ℂ) (p : X × H) : ℂ :=
  complexUnequalDualKernel h W (ρ p.2 V) s p.1 *
    squareKernel d.inv (splitSquareTransform a Φ) (fun _ => 1) s (ι p.2)

private theorem pair_denominator_cons (d : ComplexCharacterData) (ds es : List ComplexCharacterData) (s : ℂ) :
    (complexPairLFactor (d :: ds) es).denominator s =
      (complexPairLFactor [d] es).denominator s * (complexPairLFactor ds es).denominator s := by
  have hL : complexPairLFactor (d :: ds) es = (complexPairLFactor [d] es).mul (complexPairLFactor ds es) := by
    simpa only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using complexLFactor_append (es.map d.mul) (complexPairBlocks ds es)
  rw [hL]
  rfl

private theorem integrate_square_then_lower {A : Type*} [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ]
    (K : A × H → ℂ) (C : A → ℂ) (S : A → H → ℂ) (J : A → ℂ) (d₁ d₂ : ℂ)
    (hK : Integrable K (μ.prod ν)) (hS : ∀ p, K p = C p.1 * S p.1 p.2)
    (hJ : ∀ x, d₁ * (∫ z, S x z ∂ν) = J x) :
    (d₁ * d₂) * (∫ p, K p ∂μ.prod ν) = d₂ * ∫ x, C x * J x ∂μ := by
  rw [integral_prod _ hK, mul_comm d₁ d₂, mul_assoc, ← integral_const_mul]
  congr 1
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  have he : (fun z => K (x, z)) = fun z => C x * S x z := funext (fun z => hS (x, z))
  rw [he, integral_const_mul, ← hJ]
  ring

private theorem ordinary_replace (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (D : ComplexQuotientMeasureData t) (Φ : 𝓢(Mat, ℂ)) (W : G (r + 1) → ℂ) (V Y : H → ℂ)
    (s : ℂ) (hi : Integrable (ordinaryFiber h d Φ W V s) (D.measure.prod ν))
    (hY : ∀ x : H, (complexPairLFactor [d] es).denominator s *
      (∫ z, squareKernel d Φ (fun g => V (x * g)) s z ∂ν) = Y x) :
    (complexPairLFactor (d :: ds) es).denominator s *
      (∫ p, ordinaryFiber h d Φ W V s p ∂D.measure.prod ν) =
      (complexPairLFactor ds es).denominator s * complexUnequalIntegral h D W Y s := by
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  rw [pair_denominator_cons]
  let C (x : Q t) := W (padGL (Nat.succ_le_succ h.le) x.out) *
    ArchimedeanLocal.detPower complexNormalizedAbs x.out (s - ((r - t : ℕ) : ℂ) / 2)
  let S (x : Q t) := squareKernel d Φ (fun g => V (x.out * g)) s
  have he := integrate_square_then_lower D.measure (ordinaryFiber h d Φ W V s) C S (fun x => Y x.out)
    ((complexPairLFactor [d] es).denominator s) ((complexPairLFactor ds es).denominator s) hi (fun p => by
      simp only [ordinaryFiber, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, C, S, squareKernel,
        ArchimedeanLocal.translateFunction, mul_one]
      ring) (fun x => hY x.out)
  rw [he, complexUnequalIntegral, ArchimedeanLocal.unequalIntegral]
  congr 1
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  unfold C ArchimedeanLocal.unequalIntegrand
  ring

private theorem reflected_replace (a : ℂˣ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (D : ComplexQuotientMeasureData t) (Φ : 𝓢(Mat, ℂ)) (W : G (r + 1) → ℂ) (V Y : H → ℂ)
    (s E : ℂ) (hi : Integrable (reflectedFiber h a d Φ W V s) ((complexUnequalDualMeasure a D).prod ν))
    (hY : ∀ x : H, (complexPairLFactor [d.inv] (es.map ComplexCharacterData.inv)).denominator s *
      (∫ z, squareKernel d.inv (splitSquareTransform a Φ) (fun g => V (x * ι g)) s z ∂ν) = E * Y x) :
    (complexPairLFactor ((d :: ds).map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
      (∫ p, reflectedFiber h a d Φ W V s p ∂(complexUnequalDualMeasure a D).prod ν) =
      E * ((complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
        ∫ p, complexUnequalDualKernel h W Y s p ∂complexUnequalDualMeasure a D) := by
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : (rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let μ : Measure X := complexUnequalDualMeasure a D
  let : SigmaFinite μ := by unfold μ complexUnequalDualMeasure; infer_instance
  rw [List.map_cons, pair_denominator_cons]
  let x₀ (p : X) : H := weylLong (t + 1) ℂ * ι p.1.out
  let C (p : X) := (ρ (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W))
    (ArchimedeanLocal.rectangularPoint h p.1.out p.2) *
    ArchimedeanLocal.detPower complexNormalizedAbs p.1.out (s - ((r - t : ℕ) : ℂ) / 2)
  let S (p : X) (z : H) := squareKernel d.inv (splitSquareTransform a Φ) (fun g => V (x₀ p * ι g)) s (ι z)
  have hι : MeasurePreserving ι ν ν := complexMatrixHaar_measurePreserving_inverseTranspose _ (matrixLebesgue _)
  have he := integrate_square_then_lower μ (reflectedFiber h a d Φ W V s) C S (fun p => E * Y (x₀ p))
    ((complexPairLFactor [d.inv] (es.map ComplexCharacterData.inv)).denominator s)
    ((complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s)
    hi (fun p => by
      simp only [reflectedFiber, complexUnequalDualKernel, ArchimedeanLocal.blockKernel, C, S, squareKernel, x₀,
        ArchimedeanLocal.translateFunction, ArchimedeanLocal.dualFunction, inverseTranspose_involutive, mul_one]
      ring) (fun p => by
      unfold S
      rw [hι.integral_comp (inverseTransposeMeasurableEquiv hι.measurable).measurableEmbedding
        (squareKernel d.inv (splitSquareTransform a Φ) (fun g => V (x₀ p * ι g)) s)]
      exact hY (x₀ p))
  have hk (p : X) : C p * (E * Y (x₀ p)) = E * complexUnequalDualKernel h W Y s p := by
    simp only [C, x₀, complexUnequalDualKernel, ArchimedeanLocal.blockKernel, ArchimedeanLocal.dualFunction]
    ring
  rw [he]
  simp_rw [hk]
  rw [integral_const_mul]
  ring

/-- In a fixed retained fiber, each normalized square trace replaces the smaller coefficient
in the corresponding lower-rank integral. -/
def ComplexGapRetainedFiberStatement : Prop :=
  ∀ (h : t < r) (a : ℂˣ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (D : ComplexQuotientMeasureData t) (Φ : 𝓢(Mat, ℂ)) (W : G (r + 1) → ℂ) (V Y Yd : H → ℂ)
    (s E : ℂ),
    (Integrable (ordinaryFiber h d Φ W V s) (D.measure.prod ν) →
      (∀ x : H, (complexPairLFactor [d] es).denominator s *
        (∫ z, squareKernel d Φ (fun g => V (x * g)) s z ∂ν) = Y x) →
      (complexPairLFactor (d :: ds) es).denominator s *
        (∫ p, ordinaryFiber h d Φ W V s p ∂D.measure.prod ν) =
        (complexPairLFactor ds es).denominator s * complexUnequalIntegral h D W Y s) ∧
    (Integrable (reflectedFiber h a d Φ W V s) ((complexUnequalDualMeasure a D).prod ν) →
      (∀ x : H, (complexPairLFactor [d.inv] (es.map ComplexCharacterData.inv)).denominator s *
        (∫ z, squareKernel d.inv (splitSquareTransform a Φ) (fun g => V (x * ι g)) s z ∂ν) = E * Yd x) →
      (complexPairLFactor ((d :: ds).map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
        (∫ p, reflectedFiber h a d Φ W V s p ∂(complexUnequalDualMeasure a D).prod ν) =
        E * ((complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
          ∫ p, complexUnequalDualKernel h W Yd s p ∂complexUnequalDualMeasure a D))

theorem complexGapRetainedFiber : ComplexGapRetainedFiberStatement (r := r) (t := t) := by
  intro h a d ds es D Φ W V Y Yd s E
  exact ⟨ordinary_replace h d ds es D Φ W V Y s, reflected_replace h a d ds es D Φ W V Yd s E⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained
