import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Induction.BlockFactors

/-!
# Tempered block factorization of whole-Levi representations

An irreducible representation of an actual standard p-adic Levi that is
analytically tempered on the whole Levi factors as the external tensor of
irreducible admissible tempered block representations, in the original carrier
universe. This is a derived statement; no proof is given here.
-/

namespace Langlands

open GeneralLinear RelativeRegularComparison

universe uF uV

/-- Every irreducible whole-Levi tempered representation of an actual standard
p-adic Levi is equivalent to the external tensor of irreducible admissible
tempered block representations whose carriers lie in its own universe. -/
def GLWholeLeviTemperedFactorizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (σ : Rep.{uV} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible σ.ρ → IsLeviTempered T B σ →
      ∃ A : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
        (∀ i, Representation.IsIrreducible (A i).representation) ∧
        (∀ i, (A i).IsAdmissible) ∧
        (∀ i, T.IsTempered (A i).representation) ∧
        Nonempty (σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation)))

end Langlands
