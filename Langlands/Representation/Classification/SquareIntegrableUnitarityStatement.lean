import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Unitary.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Unitarizability from square-integrable matrix coefficients

This proposition states Casselman's square-integrable unitarity theorem for
positive-rank p-adic general linear groups. It does not prove the theorem.
-/

namespace Langlands

universe uF uV

/-- Every irreducible analytically square-integrable positive-rank p-adic GL
representation admits an invariant positive definite Hermitian form on its
original algebraic carrier. -/
def GLSquareIntegrableUnitarityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      Representation.IsIrreducible ρ → T.IsSquareIntegrable ρ → IsUnitarizable ρ

end Langlands
