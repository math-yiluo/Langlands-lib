import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviAdmissibleFactorizationStatement
open Langlands.GeneralLinear
universe uF uW

/-- Every admissible irreducible representation of an actual standard p-adic
Levi is equivalent to the external tensor of admissible irreducible block
representations whose carriers lie in the universe of the given carrier. -/
def PadicLeviAdmissibleFactorizationStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier),
      σ.IsIrreducible → σ.IsAdmissible →
      ∃ A : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier),
        (∀ i, (A i).IsIrreducible) ∧ (∀ i, (A i).IsAdmissible) ∧
        Nonempty (σ.representation.Equiv
          (B.blockTensor (fun i => (A i).representation)))

end Langlands.AllFieldBZ.CuspidalSupport
