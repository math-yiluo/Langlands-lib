import Langlands.Representation.Classification.LanglandsData

/-!
# Regular Langlands block-rank and real-parameter uniqueness

The parabolic and real-parameter part of Silberger's Proposition 6.1, expressed
using the existing ordered tempered data and arbitrary irreducible quotients.
This proposition definition does not recover the tempered block classes.
-/

namespace Langlands

open CategoryTheory

universe uF uV

/-- Isomorphic irreducible quotients of regular tempered standard modules
determine the ordered block ranks and real determinant exponents. -/
def GLRegularLanglandsParameterUniquenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (d e : T.TemperedLanglandsDatum.{max uF uV, uF} n)
        (π τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
        d.IsLanglandsQuotient π → e.IsLanglandsQuotient τ →
        Nonempty (π ≅ τ) →
          ∃ a : Fin d.shape.length ≃o Fin e.shape.length,
            ∀ i, d.shape.size i = e.shape.size (a i) ∧
              d.exponent i = e.exponent (a i)

end Langlands
