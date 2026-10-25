import Langlands.Representation.Classification.TemperedBlockStatement

/-!
# Irreducibility of square-integrable block induction

The irreducibility conclusion of `SquareIntegrableBlockInduction`, with the
same actual blocks, analytic hypotheses and normalized upper induction.
This proposition definition states the source-derived target; it proves no
induction or classification theorem.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Normalized upper product induction of irreducible, analytically
square-integrable, unitarizable GL blocks is irreducible. -/
def SquareIntegrableBlockInductionIrreducibility : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, Representation.IsIrreducible (σ i).representation ∧
      T.IsSquareIntegrable (σ i).representation ∧ IsUnitarizable (σ i).representation) →
    let I := (T.normalizedProductInductionFunctor B).obj σ
    Representation.IsIrreducible I.representation

end Langlands.Classification
