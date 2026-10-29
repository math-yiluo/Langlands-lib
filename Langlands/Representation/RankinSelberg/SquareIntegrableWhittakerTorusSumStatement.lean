import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Representation.Classification.Tempered

/-!
# Square-integrable Whittaker functions on the torus modulo the center

For an irreducible square-integrable representation of `GL_(m+1)`, every
coefficient-model Whittaker function is square-summable on the uniformizer
lattice of the diagonal torus with last exponent zero, against the inverse
upper-Borel modulus. This module defines a proposition; it does not prove it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

/-- For an irreducible square-integrable representation of `GL_(m+1)`, every
coefficient-model vector `W` and every uniformizing element `ϖ`, the family
`δ(ϖ^μ)⁻¹ ‖W(ϖ^μ)‖²` is summable over the exponent vectors `μ = (λ, 0)` with
`λ ∈ ℤ^m`, where `δ(a) = ∏_{i<j} |a_i / a_j|` is the upper-Borel modulus for
the normalized absolute value of the supplied topology. -/
def SquareIntegrableWhittakerTorusSumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (m : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V,
    Representation.IsIrreducible π → T.IsSquareIntegrable π →
    ∀ (ℓ : glFunctionals ψ m π) (f : (coefficientModel π ℓ).toSubmodule)
      (ϖ : F.Carrierˣ),
      Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
      let μ : (Fin m → ℤ) → Fin (m + 1) → ℤ := fun lam => Fin.snoc lam 0
      Summable (fun lam : Fin m → ℤ =>
        (∏ i : Fin (m + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => i < j),
          T.normalizedAbs ((ϖ ^ μ lam i / ϖ ^ μ lam j : F.Carrierˣ) : F.Carrier))⁻¹ *
          ‖f.val.val (Iwasawa.torus ϖ (μ lam))‖ ^ 2)

end Langlands.RankinSelberg
