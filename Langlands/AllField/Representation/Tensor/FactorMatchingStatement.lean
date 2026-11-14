import Langlands.Representation.Tensor.FactorMatchingStatement
import Langlands.AllField.Representation.Induction.BlockFactors
/-! Multiplicity-sensitive composition-factor matching for finite external
tensors of admissible smooth complex representations of p-adic GL blocks.
This is a derived statement target. -/

namespace Langlands.AllField.FiniteTensor
open Langlands.FiniteTensor hiding PadicExternalTensorFactorsTheorem
open Langlands.AllField.FiniteTensor

open Langlands.GeneralLinear

universe uF uV uW

/-- Factorwise Jordan–Hölder matching of admissible smooth block
representations induces matching for their actual external tensor products. -/
def PadicExternalTensorFactorsTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ (A : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F))
      (A' : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F)),
      (∀ i, (A i).IsAdmissible) →
      (∀ i, (A' i).IsAdmissible) →
      (∀ i, HaveSameJordanHolderFactors
        (Rep.of (A i).representation) (Rep.of (A' i).representation)) →
      HaveSameJordanHolderFactors
        (Rep.of (B.blockTensor (fun i => (A i).representation)))
        (Rep.of (B.blockTensor (fun i => (A' i).representation)))

end Langlands.AllField.FiniteTensor
