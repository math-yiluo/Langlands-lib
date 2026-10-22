import Langlands.Weil.ArchimedeanRepresentation
import Langlands.Weil.Representation.SumsTensor
import Langlands.LocalFactor.Archimedean.Definitions

/-!
# Independence of archimedean arithmetic factor presentations

The presentations are finite sums of actual continuous character representations,
including the actual two-dimensional real induction model. Their arithmetic
factors use the published reciprocal-entire Gamma constructions.
No classification, reciprocity identification, or local-constant system is assumed.
-/

noncomputable section

namespace Langlands.LocalFactor

open Langlands.Weil.Archimedean

/-- Choice independence of complex arithmetic factors, on genuine finite
character presentations and actual invertible linear intertwiners. -/
def ComplexFactorPresentationIndependenceStatement : Prop :=
  let Data := (ℂˣ →ₜ* ℂˣ) × (ℤ × ℂ)
  let compatible (d : Data) : Prop :=
    ∀ z : ℂˣ, (d.1 z : ℂ) =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ d.2.1 *
        (‖(z : ℂ)‖ : ℂ) ^ (2 * d.2.2)
  let model (ds : List Data) : FiniteRepresentation ℂ ComplexWeil :=
    ds.foldr (fun d A => FiniteRepresentation.sum (complexCharacter d.1).val A)
      (FiniteRepresentation.of (Representation.trivial ℂ ComplexWeil (Fin 0 → ℂ)))
  let lFactor (ds : List Data) : ReciprocalEntire :=
    ReciprocalEntire.product (ds.map fun d =>
      Archimedean.gammaComplex.shift (d.2.2 + (d.2.1.natAbs : ℂ) / 2))
  let standardEpsilon (ds : List Data) : ℂ :=
    (ds.map fun d => Complex.I ^ d.2.1.natAbs).prod
  let epsilon (ds : List Data) (a : ℂˣ) (c : NNReal) (s : ℂ) : ℂ :=
    (c : ℂ) ^ ds.length * (ds.map fun d => (d.1 a : ℂ)).prod *
      (‖(a : ℂ)‖ : ℂ) ^ (2 * (ds.length : ℂ) * (s - 1)) *
      standardEpsilon ds
  (∀ ds : List Data, (∀ d ∈ ds, compatible d) →
    ∀ (a : ℂˣ) (c : NNReal), 0 < c →
      Differentiable ℂ (epsilon ds a c) ∧
      ∀ s : ℂ, epsilon ds a c s ≠ 0) ∧
  (∀ ds es : List Data,
    (∀ d ∈ ds, compatible d) → (∀ e ∈ es, compatible e) →
    Nonempty (FiniteRepresentation.Equiv (model ds) (model es)) →
      lFactor ds = lFactor es ∧
      standardEpsilon ds = standardEpsilon es ∧
      ∀ (a : ℂˣ) (c : NNReal), 0 < c →
        ∀ s : ℂ, epsilon ds a c s = epsilon es a c s)

/-- Choice independence of real arithmetic factors for sums of real characters
and actual inductions from complex characters, including the reducible
weight-zero induction. The induced epsilon includes the lambda factor `i`. -/
def RealFactorPresentationIndependenceStatement : Prop :=
  let RealData := (ℝˣ →ₜ* ℂˣ) × (Fin 2 × ℂ)
  let ComplexData := (ℂˣ →ₜ* ℂˣ) × (ℤ × ℂ)
  let Data := RealData ⊕ ComplexData
  let compatible (d : Data) : Prop :=
    match d with
    | .inl r => ∀ x : ℝˣ, (r.1 x : ℂ) =
        (((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ) ^ r.2.1.val *
          ((|(x : ℝ)| : ℝ) : ℂ) ^ r.2.2
    | .inr z => ∀ x : ℂˣ, (z.1 x : ℂ) =
        ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ z.2.1 *
          (‖(x : ℂ)‖ : ℂ) ^ (2 * z.2.2)
  let blockModel (d : Data) : FiniteRepresentation ℂ RealWeil :=
    match d with
    | .inl r => (realCharacter r.1).val
    | .inr z => (realInducedCharacter z.1).val
  let model (ds : List Data) : FiniteRepresentation ℂ RealWeil :=
    ds.foldr (fun d A => FiniteRepresentation.sum (blockModel d) A)
      (FiniteRepresentation.of (Representation.trivial ℂ RealWeil (Fin 0 → ℂ)))
  let blockFactor (d : Data) : ReciprocalEntire :=
    match d with
    | .inl r => Archimedean.gammaReal.shift (r.2.2 + (r.2.1.val : ℂ))
    | .inr z => Archimedean.gammaComplex.shift (z.2.2 + (z.2.1.natAbs : ℂ) / 2)
  let lFactor (ds : List Data) : ReciprocalEntire :=
    ReciprocalEntire.product (ds.map blockFactor)
  let blockEpsilon (d : Data) : ℂ :=
    match d with
    | .inl r => Complex.I ^ r.2.1.val
    | .inr z => Complex.I ^ (z.2.1.natAbs + 1)
  let standardEpsilon (ds : List Data) : ℂ := (ds.map blockEpsilon).prod
  let blockRank (d : Data) : ℕ :=
    match d with
    | .inl _ => 1
    | .inr _ => 2
  let rank (ds : List Data) : ℕ := (ds.map blockRank).sum
  let realToComplex (x : ℝˣ) : ℂˣ := Units.map Complex.ofRealHom.toMonoidHom x
  let blockDeterminant (d : Data) (a : ℝˣ) : ℂ :=
    match d with
    | .inl r => (r.1 a : ℂ)
    | .inr z =>
        (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) * (z.1 (realToComplex a) : ℂ)
  let epsilon (ds : List Data) (a : ℝˣ) (c : NNReal) (s : ℂ) : ℂ :=
    (c : ℂ) ^ rank ds * (ds.map fun d => blockDeterminant d a).prod *
      ((|(a : ℝ)| : ℝ) : ℂ) ^ ((rank ds : ℂ) * (s - 1)) *
      standardEpsilon ds
  (∀ ds : List Data, (∀ d ∈ ds, compatible d) →
    ∀ (a : ℝˣ) (c : NNReal), 0 < c →
      Differentiable ℂ (epsilon ds a c) ∧
      ∀ s : ℂ, epsilon ds a c s ≠ 0) ∧
  (∀ ds es : List Data,
    (∀ d ∈ ds, compatible d) → (∀ e ∈ es, compatible e) →
    Nonempty (FiniteRepresentation.Equiv (model ds) (model es)) →
      lFactor ds = lFactor es ∧
      standardEpsilon ds = standardEpsilon es ∧
      ∀ (a : ℝˣ) (c : NNReal), 0 < c →
        ∀ s : ℂ, epsilon ds a c s = epsilon es a c s)

/-- Separate L- and epsilon-factor independence for the concrete archimedean
presentations used by an arithmetic factor attachment. -/
def ArchimedeanFactorPresentationIndependenceStatement : Prop :=
  ComplexFactorPresentationIndependenceStatement ∧
  RealFactorPresentationIndependenceStatement

end Langlands.LocalFactor
