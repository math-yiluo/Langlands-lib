import Langlands.LocalFactor.NonabelianSystem
import Langlands.VirtualRepresentation.ExactDeterminant

/-!
# Additive-character scaling for actual local-constant systems

Deligne's fixed-Haar law on the continuous exact virtual group. This is a
proposition only; it uses the existing system specification without assuming
its existence or adjoining the desired scaling law to that specification.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

/-- Deligne 5.4: change the nontrivial additive character by a nonzero scalar,
retain the same Haar measure, and use the actual virtual determinant and degree.
The Weil lift is quantified explicitly to evaluate the determinant through the
supplied normalized reciprocity family, without selecting an inverse. -/
def AdditiveCharacterScalingStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F),
    IsSystem F e ε →
    ∀ E : Extension F,
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
      (a : E.fieldˣ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      ∀ x : Virtual.{uF, uV} F E,
      (ε E (ψ.scale a) μ x : ℂ) =
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E) x w : ℂ) *
          ((fieldData F E).normalizedAbs (a : E.field) : ℂ) ^ (-degree F E x) *
          (ε E ψ μ x : ℂ)

end Langlands.LocalFactor.NonabelianSystem
