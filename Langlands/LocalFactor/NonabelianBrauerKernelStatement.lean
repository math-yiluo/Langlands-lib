import Langlands.LocalFactor.NonabelianBrauerPresentation

/-! # Arithmetic compatibility of actual abelian epsilon ratios -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Actual products of abelian epsilon ratios are trivial on all relations among
induced continuous character differences. This is a proposition only. -/
def KernelCompatibility (e : ReciprocityFamily F) : Prop :=
  NormalizedReciprocity F e →
    ∀ (E : Extension F) (ψ : AdditiveCharacter F E) (measures : HaarFamily F)
      (z : Presentation F E),
      presentationMap.{uF, uV} F e E z = 0 → evaluationMap F E ψ measures z = 0

/-- The arithmetic kernel assertion for all actual finite p-adic fields and
independent representation-carrier universes. -/
def KernelCompatibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (e : ReciprocityFamily F),
    KernelCompatibility.{uF, uV} F e

end Langlands.LocalFactor.NonabelianBrauer
