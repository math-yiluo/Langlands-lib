import Langlands.Representation.Classification.TadicComplementarySeriesStatement

/-!
# The open-interval clause of Tadic's complementary-series unitarity

This proposition isolates the first conclusion of Tadic 1986, Proposition 2.9.
The full published proposition retains its separate endpoint conclusion.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The open-interval conclusion of Tadic 1986 Proposition 2.9: the actual
complementary product is unitarizable throughout any symmetric open interval
on which it remains irreducible, for an irreducible unitarizable block. -/
def ComplementarySeriesOpenIntervalUnitarity : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (hn : 0 < n)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (α₀ : ℝ),
    Representation.IsIrreducible σ.representation → IsUnitarizable σ.representation →
      0 < α₀ →
      (∀ α ∈ Set.Ioo (-α₀) α₀,
        Representation.IsIrreducible (complementaryProduct F T hn σ α).representation) →
      ∀ α ∈ Set.Ioo (-α₀) α₀,
        IsUnitarizable (complementaryProduct F T hn σ α).representation

end Langlands.Classification
