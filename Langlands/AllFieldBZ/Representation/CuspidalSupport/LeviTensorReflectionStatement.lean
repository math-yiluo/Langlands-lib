import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalContragredientStatement
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviTensorSupercuspidalReflectionStatement
open Langlands.GeneralLinear
universe uF uW

/-- Quasicuspidality of the actual block tensor forces supercuspidality of
each irreducible admissible smooth factor. -/
def PadicLeviTensorSupercuspidalReflectionStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ A : ∀ i : Fin B.length,
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier),
      (∀ i, (A i).IsIrreducible) →
      (∀ i, (A i).IsAdmissible) →
      IsLeviQuasicuspidal B (B.blockTensor (fun i => (A i).representation)) →
      ∀ i, GeneralLinear.IsSupercuspidal (A i).representation

end Langlands.AllFieldBZ.CuspidalSupport
