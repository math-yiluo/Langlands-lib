import Langlands.LocalFactor.EpsilonZeroStatement
import Langlands.VirtualRepresentation.ExactDeterminant

/-!
# The modified local constant on the exact virtual group

The extension is specified by its values on actual genuine representations.
Existence, uniqueness, character and Haar scaling, and induction are
propositions only.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.EpsilonZero

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A multiplicative extension of the constructed genuine `ε₀` value to the
continuous exact Grothendieck group, at a fixed spectral parameter. This
predicate contains neither the Haar law nor the induction law. -/
def IsVirtualExtension (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (s : ℂ)
    (ε₀ : NonabelianSystem.Assignment.{uF, uV} F) : Prop :=
  NonabelianSystem.AdditiveRelation F ε₀ ∧
    ∀ (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
      (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
      (hA : A.IsContinuous) (Φ : CommonClosureWeilDeligne.GeometricFrobenius F E),
      (ε₀ E ψ μ (genuineClass F E A hA) : ℂ) =
        value F e ε hε E ψ μ A hA Φ s

/-- Deligne (5.4) at a fixed spectral parameter on exact virtual classes.
The Haar measure is retained; both dimension exponents are integers. -/
def VirtualAdditiveCharacterScaling (e : ReciprocityFamily F) (s : ℂ)
    (ε₀ : NonabelianSystem.Assignment.{uF, uV} F) : Prop :=
  ∀ E : Extension F,
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
      (a : E.fieldˣ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      ∀ x : Virtual.{uF, uV} F E,
      (ε₀ E (ψ.scale a) μ x : ℂ) =
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x w : ℂ) *
          (CommonClosureSpectral.character F E s w : ℂ) ^ degree F E x *
          ((fieldData F E).normalizedAbs (a : E.field) : ℂ) ^ (-degree F E x) *
          (ε₀ E ψ μ x : ℂ)

/-- Deligne (5.3): arbitrary regular Haar measures give the same value on the
actual kernel of virtual dimension. -/
def DegreeZeroHaarIndependence (ε₀ : NonabelianSystem.Assignment.{uF, uV} F) : Prop :=
  ∀ (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ μ' : HaarMeasure F E) (x : DegreeZero.{uF, uV} F E),
    ε₀ E ψ μ x.val = ε₀ E ψ μ' x.val

/-- Deligne (5.6.2) on all exact virtual classes, with the same ordinary
epsilon lambda factor and the integer virtual dimension as exponent. -/
def VirtualInductionCorrection (ε ε₀ : NonabelianSystem.Assignment.{uF, uV} F) : Prop :=
  ∀ (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (μL : HaarMeasure F L)
    (x : Virtual.{uF, uV} F L),
    let ψL := traceCharacter F E L h ψ
    let one : Virtual.{uF, uV} F L :=
      ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ)
    let lam := ε E ψ μ (induce F E L h one) * (ε L ψL μL one)⁻¹
    ε₀ E ψ μ (induce F E L h x) =
      lam ^ degree F L x * ε₀ L ψL μL x

end Langlands.LocalFactor.EpsilonZero

namespace Langlands.LocalFactor

open CommonClosure

/-- Deligne (5.2), (5.3), (5.4), (5.6.1) and (5.6.2) for virtual `ε₀`, including the
unique extension of the actual genuine formula at every spectral parameter.
No existence or law for this extension is assumed in the hypotheses. -/
def EpsilonZeroVirtualStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (s : ℂ),
    (∃! ε₀ : NonabelianSystem.Assignment.{uF, uV} F,
      EpsilonZero.IsVirtualExtension F e ε hε s ε₀) ∧
    ∀ ε₀ : NonabelianSystem.Assignment.{uF, uV} F,
      EpsilonZero.IsVirtualExtension F e ε hε s ε₀ →
        NonabelianSystem.HaarScalingRelation F ε₀ ∧
          EpsilonZero.DegreeZeroHaarIndependence F ε₀ ∧
          EpsilonZero.VirtualAdditiveCharacterScaling F e s ε₀ ∧
            NonabelianSystem.InductionRelation F ε₀ ∧
            EpsilonZero.VirtualInductionCorrection F ε ε₀

end Langlands.LocalFactor
