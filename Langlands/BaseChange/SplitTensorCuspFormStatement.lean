import Langlands.BaseChange.CuspForm
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Split tensor products of test functions and cusp forms

At a place that splits completely, `GL_n(F^l) = GL_n(F)^l`. For test functions
`φ_0, …, φ_{l-1}` on `GL_n(F)`, the tensor product `splitTensor φ` is a test function on
`GL_n(F^l)`, and it has vanishing constant terms as soon as one factor has.
This module defines an unproved proposition. See the paired Markdown.
-/

namespace Langlands.BaseChange

universe u

open HarmonicAnalysis

/-- **Split tensor products of test functions and cusp forms.** For every nonarchimedean
local field `F`, all `n l : ℕ` and all `φ : Fin l → C^∞_c(GL_n(F))`, with `Fin l → F` carrying
the product topology:
(a) `splitTensor (fun i => φ i)` is locally constant with compact support on `GL_n(F^l)`;
(b) if some factor `φ i₀` has vanishing constant terms over `F`, then
`splitTensor (fun i => φ i)` has vanishing constant terms over `F^l`. -/
def SplitTensorCuspFormStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n l : ℕ) (φ : Fin l → SchwartzBruhat (GeneralLinear n F)),
    splitTensor (fun i => (φ i : GeneralLinear n F → ℂ)) ∈
        schwartzBruhatSubmodule (GeneralLinear n (Fin l → F)) ∧
      ∀ i₀ : Fin l, HasVanishingConstantTerms (φ i₀ : GeneralLinear n F → ℂ) →
        HasVanishingConstantTerms (splitTensor (fun i => (φ i : GeneralLinear n F → ℂ)))

end Langlands.BaseChange
