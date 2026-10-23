import Langlands.Representation.Classification.LanglandsData

/-!
# Recovery of the untwisted tensor at a fixed regular parameter

This proposition isolates the fixed-shape, fixed-exponent recovery consequence
of Silberger's Proposition 6.1. It has no proof here.
-/

namespace Langlands

open CategoryTheory

universe uF uV

/-- Isomorphic irreducible quotients at one strictly decreasing real parameter
recover the actual untwisted tensor of the irreducible tempered block factors. -/
def GLRegularLanglandsTensorRecoveryStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (B : GeneralLinear.BlockShape n)
        (σ σ' : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (B.size i) F.Carrier))
        (hσ : ∀ i, Representation.IsIrreducible (σ i).representation)
        (hσ' : ∀ i, Representation.IsIrreducible (σ' i).representation)
        (htσ : ∀ i, T.IsTempered (σ i).representation)
        (htσ' : ∀ i, T.IsTempered (σ' i).representation)
        (t : Fin B.length → ℝ) (ht : StrictAnti t)
        (π τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
        (PadicField.TopologicalData.TemperedLanglandsDatum.mk B σ hσ htσ t ht
          : T.TemperedLanglandsDatum n).IsLanglandsQuotient π →
        (PadicField.TopologicalData.TemperedLanglandsDatum.mk B σ' hσ' htσ' t ht
          : T.TemperedLanglandsDatum n).IsLanglandsQuotient τ →
        Nonempty (π ≅ τ) →
        Nonempty ((B.blockTensor (fun i => (σ i).representation)).Equiv
          (B.blockTensor (fun i => (σ' i).representation)))

end Langlands
