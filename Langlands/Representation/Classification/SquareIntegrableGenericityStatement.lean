import Langlands.Representation.Category.Basic
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Whittaker genericity of a square-integrable representation

The intrinsic single-representation statement uses analytic square-integrability
modulo the center, an actual invariant positive Hermitian form, and the standard
upper-unipotent character. No genericity or induction theorem is proved here.
-/

namespace Langlands.Classification

open HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every irreducible analytically square-integrable unitarizable smooth
positive-rank GL representation is generic for every continuous nontrivial
unitary additive character, including in rank one. -/
def SquareIntegrableGenericity : Prop :=
  letI := T.topology
  ∀ (n : ℕ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
    Representation.IsIrreducible π.representation →
      T.IsSquareIntegrable π.representation →
      IsUnitarizable π.representation →
      ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
        Whittaker.IsGeneric ψ n π.representation

end Langlands.Classification
