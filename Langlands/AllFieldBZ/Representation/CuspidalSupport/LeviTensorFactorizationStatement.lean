import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviCuspidalFactorizationStatement
open Langlands.GeneralLinear
universe uF uW uV

/-- Every irreducible cuspidal representation of an actual standard p-adic
Levi is equivalent to the external tensor of irreducible supercuspidal block
representations, whose carriers lie in an independently prescribed universe. -/
def PadicLeviCuspidalFactorizationStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      ∃ A : ∀ i : Fin B.length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i),
        Nonempty (σ.representation.Equiv
          (B.blockTensor (fun i => (A i).obj.representation)))

end Langlands.AllFieldBZ.CuspidalSupport
