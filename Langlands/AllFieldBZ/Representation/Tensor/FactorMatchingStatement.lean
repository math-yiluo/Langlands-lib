import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Tensor.FactorMatchingStatement

/-!
# All-field port of `Langlands.Representation.Tensor.FactorMatchingStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Tensor.FactorMatchingStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.FiniteTensor
open Langlands.FiniteTensor hiding PadicExternalTensorFactorsTheorem
open Langlands.GeneralLinear
universe uF uV uW

/-- Factorwise Jordan–Hölder matching of admissible smooth block
representations induces matching for their actual external tensor products. -/
def PadicExternalTensorFactorsTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
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

end Langlands.AllFieldBZ.FiniteTensor
