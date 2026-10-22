import Langlands.LocalFactor.ConductorExponentStatement
import Langlands.LocalFactor.NonabelianDualityStatement
import Langlands.VirtualRepresentation.ExactDeterminant

/-!
# Langlands' normalization of the local constants of a supplied system

Tate's (3.6.2) and (3.6.6)–(3.6.9) for Langlands' constant
`ε_L(V, ψ) = ε_D(V ω_(1/2), ψ, dx_ψ)` of a supplied common-closure
local-constant system, with `dx_ψ` a supplied self-dual measure. Deligne's
(5.7.2) for Deligne's constant of a unitary representation is stated at the
bottom intermediate field of the closure, where Artin conductors are read off
from actual finite-inertia presentations. These are propositions; no system,
self-dual measure or dual measure is constructed.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.LanglandsNormalization

open CommonClosure CommonClosureSpectral VirtualRepresentation
open ConductorExponent

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Tate (3.6.2): `ε_D(V, ψ, dx) = (dx/dx_ψ)^(dim V) ε_L(V ω_(-1/2), ψ)`, at every
Haar measure `dx = c dx_ψ` and every exact virtual `V`. -/
def DeligneFromLanglandsStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ) (c : NNReal) (hc : 0 < c)
    (x : Virtual.{uF, uV} F E),
    ε E ψ (scaleHaar F E μ.val c hc) x =
      NonabelianSystem.positiveScale c hc ^ degree F E x *
        conditionalLanglandsConstant F e ε hε E ψ μ (virtualTwist F E (-(1 / 2)) x)

/-- Tate (3.6.6): `ε_L(V, ψ_a) = det V(a) ε_L(V, ψ)`, with `ψ_a(y) = ψ(a y)`,
self-dual measures for both characters, and `det V(a)` evaluated at any Weil
element whose image under the supplied reciprocity is `a`. -/
def AdditiveCharacterScalingStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F),
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ)
      (a : E.fieldˣ) (μa : SelfDualMeasure F E (ψ.scale a)) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      ∀ x : Virtual.{uF, uV} F E,
        conditionalLanglandsConstant F e ε hε E (ψ.scale a) μa x =
          ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x w *
            conditionalLanglandsConstant F e ε hε E ψ μ x

/-- Tate (3.6.7): `ε_L(V, ψ) ε_L(V*, ψ⁻¹) = 1`, with `ψ⁻¹(y) = ψ(-y)`, and its
centered spectral form `ε_L(s, V, ψ) ε_L(1 - s, V*, ψ⁻¹) = 1`. -/
def DualityStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F),
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ)
      (μ' : SelfDualMeasure F E (ψ.scale (-1))) (x : Virtual.{uF, uV} F E),
      conditionalLanglandsConstant F e ε hε E ψ μ x *
          conditionalLanglandsConstant F e ε hε E (ψ.scale (-1)) μ'
            (ExactGrothendieckGroup.continuousDual x) = 1 ∧
        ∀ s : ℂ,
          conditionalLanglandsValue F e ε hε E ψ μ x s *
            conditionalLanglandsValue F e ε hε E (ψ.scale (-1)) μ'
              (ExactGrothendieckGroup.continuousDual x) (1 - s) = 1

/-- Tate (3.6.8): `ε_L(V, ψ) ε_L(V*, ψ) = det V(-1)`, with `det V(-1)` evaluated
at any Weil element whose image under the supplied reciprocity is `-1`. -/
def ContragredientProductStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F),
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = -1 →
      ∀ x : Virtual.{uF, uV} F E,
        conditionalLanglandsConstant F e ε hε E ψ μ x *
            conditionalLanglandsConstant F e ε hε E ψ μ
              (ExactGrothendieckGroup.continuousDual x) =
          ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x w

/-- Tate (3.6.9): `|ε_L(V, ψ)| = 1` for a genuine continuous unitary `V`. -/
def UnitaryAbsoluteValueStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hA : A.IsContinuous), A.IsUnitary →
    ‖(conditionalLanglandsConstant F e ε hε E ψ μ
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) ⟨A, hA⟩) : ℂ)‖ = 1

/-- Deligne (5.7.2): for a genuine continuous unitary `V` of the base and the
Fourier dual `dx' = c dx` of `dx` relative to `ψ`,
`|ε(V, ψ, dx)|^2 = (dx'/dx)^(-dim V) q^(a(V) + dim V n(ψ))`, with `a(V)` computed at
any actual presentation. -/
def DeligneAbsoluteValueStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (_hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F)) (c : NNReal) (hc : 0 < c),
    NonabelianSystem.FourierDualMeasures F (base F) ψ μ (scaleHaar F (base F) μ c hc) →
    ∀ (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
      (hA : A.IsContinuous), A.IsUnitary →
    ∀ (P : Presentation.{uF, uV} F A)
      (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension)),
      ‖(ε (base F) ψ μ (baseClass F A hA) : ℂ)‖ ^ 2 =
        (c : ℝ) ^ (-(A.rank : ℤ)) *
          baseCardinality F ^
            (((P.artinConductor hsurj : ℚ) : ℝ) + (additiveConductor F ψ : ℝ) * (A.rank : ℝ))

end Langlands.LocalFactor.LanglandsNormalization

namespace Langlands.LocalFactor

/-- Tate (3.6.2), (3.6.6)–(3.6.9) and Deligne (5.7.2), for every p-adic field and
every supplied local-constant system on its common closure. -/
def LanglandsNormalizationStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
    LanglandsNormalization.DeligneFromLanglandsStatement.{uF, uV} F ∧
      LanglandsNormalization.AdditiveCharacterScalingStatement.{uF, uV} F ∧
      LanglandsNormalization.DualityStatement.{uF, uV} F ∧
      LanglandsNormalization.ContragredientProductStatement.{uF, uV} F ∧
      LanglandsNormalization.UnitaryAbsoluteValueStatement.{uF, uV} F ∧
      LanglandsNormalization.DeligneAbsoluteValueStatement.{uF, uV} F

end Langlands.LocalFactor
