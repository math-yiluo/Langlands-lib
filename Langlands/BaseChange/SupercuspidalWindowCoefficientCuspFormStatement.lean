import Langlands.BaseChange.CuspForm
import Langlands.BaseChange.DeterminantWindow
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Cut-off coefficients of supercuspidal representations are cusp forms

The statement that, for a nonarchimedean local field `F`, a finite field extension `E` of `F`
with its module topology and a supercuspidal representation `τ` of `GL_n(E)`, every
coefficient `x ↦ λ(τ(x)⁻¹ v)` of the contragredient, multiplied by a determinant window and by
a locally constant function of the determinant, is a Schwartz–Bruhat function with vanishing
constant terms. Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F`, a field `E` finite over `F` with its module topology,
and `0 < n`, let `τ` be a supercuspidal representation of `GL_n(E)` on `W : Type uW`. For every
`m : ℕ`, every locally constant `ψ : Eˣ → ℂ`, every `v ∈ W` and every smooth linear form `λ`,
there is a Schwartz–Bruhat function `φ` on `GL_n(E)` with
`φ(x) = b_m(x) ψ(det x) λ(τ(x)⁻¹ v)` for all `x`, where `b_m = determinantWindow F m` is the
indicator of `0 ≤ ord_F N_{E/F}(det x) < m`, and `φ` has vanishing constant terms. -/
def SupercuspidalWindowCoefficientCuspFormStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [Field E] [Algebra F E] [Module.Finite F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (n : ℕ), 0 < n →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W), GeneralLinear.IsSupercuspidal τ →
      ∀ (m : ℕ) (ψ : Eˣ → ℂ), IsLocallyConstant ψ → ∀ (v : W) (ℓ : SmoothDual τ),
      ∃ φ : SchwartzBruhat (GeneralLinear n E),
        (∀ x : GeneralLinear n E, φ x = determinantWindow F m x *
          ψ (GeneralLinear.determinant x) * (ℓ : Module.Dual ℂ W) (τ x⁻¹ v)) ∧
        HasVanishingConstantTerms (φ : GeneralLinear n E → ℂ)

end Langlands.BaseChange
