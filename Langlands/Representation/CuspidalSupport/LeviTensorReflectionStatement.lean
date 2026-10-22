import Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
import Langlands.Representation.Induction.BlockFactors

/-! Supercuspidality of the factors of a quasicuspidal standard-Levi tensor.
This is a derived proposition target, not a proof of reflection. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uW

/-- Quasicuspidality of the actual block tensor forces supercuspidality of
each irreducible admissible smooth factor. -/
def PadicLeviTensorSupercuspidalReflectionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ A : ∀ i : Fin B.length,
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier),
      (∀ i, (A i).IsIrreducible) →
      (∀ i, (A i).IsAdmissible) →
      IsLeviQuasicuspidal B (B.blockTensor (fun i => (A i).representation)) →
      ∀ i, GeneralLinear.IsSupercuspidal (A i).representation

end Langlands.CuspidalSupport
