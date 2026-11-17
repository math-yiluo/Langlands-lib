import Langlands.BaseChange.CuspForm
import Langlands.Representation.Hecke.Convolution
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Cusp forms form a two-sided ideal of the Hecke algebra of `GL_n(F)`

For a nonarchimedean local field `F`, every Haar measure `μ` on `GL_n(F)` and test functions
`f g`, the convolution `(f * g)(x) = ∫ f(y) g(y⁻¹ x) dμ(y)` (the Library's
`Hecke.TestFunction.convolution`) has vanishing constant terms as soon as `f` or `g` has.
This module defines an unproved proposition. See the paired Markdown.
-/

namespace Langlands.BaseChange

universe u

open MeasureTheory HarmonicAnalysis

/-- **Cusp forms form a two-sided ideal.** For every nonarchimedean local field `F`, every
`n`, every Haar measure `μ` on `GL_n(F)` (Borel σ-algebra) and all `f g ∈ C^∞_c(GL_n(F))`:
if `g` has vanishing constant terms, so has `f * g`; and if `f` has vanishing constant terms,
so has `f * g`. -/
def CuspFormConvolutionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ),
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
      (f g : SchwartzBruhat (GeneralLinear n F)),
      (HasVanishingConstantTerms (g : GeneralLinear n F → ℂ) →
        HasVanishingConstantTerms
          (Hecke.TestFunction.convolution μ f g : GeneralLinear n F → ℂ)) ∧
      (HasVanishingConstantTerms (f : GeneralLinear n F → ℂ) →
        HasVanishingConstantTerms
          (Hecke.TestFunction.convolution μ f g : GeneralLinear n F → ℂ))

end Langlands.BaseChange
