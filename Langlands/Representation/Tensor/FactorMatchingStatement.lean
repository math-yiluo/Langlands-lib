import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Filtration.ObjectDefinitions

/-! Multiplicity-sensitive composition-factor matching for finite external
tensors of admissible smooth complex representations of p-adic GL blocks.
This is a derived statement target. -/

namespace Langlands.FiniteTensor

open GeneralLinear

universe uF uV uW

/-- Factorwise Jordan–Hölder matching of admissible smooth block
representations induces matching for their actual external tensor products. -/
def PadicExternalTensorFactorsTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ (A : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (A' : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, (A i).IsAdmissible) →
      (∀ i, (A' i).IsAdmissible) →
      (∀ i, HaveSameJordanHolderFactors
        (Rep.of (A i).representation) (Rep.of (A' i).representation)) →
      HaveSameJordanHolderFactors
        (Rep.of (B.blockTensor (fun i => (A i).representation)))
        (Rep.of (B.blockTensor (fun i => (A' i).representation)))

end Langlands.FiniteTensor
