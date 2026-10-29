import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityStatement

/-!
# From necessary upper bounds to opposite full-dual prefixes

These proposition definitions separate the algebraic change of Jacquet
convention from the analytic necessity theorem. They prove neither result.
-/

namespace Langlands

open GeneralLinear
open scoped BigOperators

universe uF uV

/-- Every actual opposite full-dual exponent of an irreducible analytically
tempered GL source has nonpositive scalar real-part prefixes. -/
def GLTemperedOppositeDualPrefixStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
      ∀ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
        (s : Fin B.length → ℝ),
        T.IsDualJacquetExponent B A χ → T.IsRealPartOf χ s →
        ∀ i : Fin B.length,
          (∑ k ∈ Finset.univ.filter (fun k : Fin B.length => k ≤ i), s k) ≤ 0

/-- The exact upper generalized-exponent necessity theorem implies the
opposite full-dual prefix bound, without adding an analytic comparison premise
to the latter. -/
def GLTemperedOppositeDualPrefixAdapterStatement : Prop :=
  GLProductLeviTemperedExponentNecessityStatement.{uF, uV} →
    GLTemperedOppositeDualPrefixStatement.{uF, uV}

end Langlands
