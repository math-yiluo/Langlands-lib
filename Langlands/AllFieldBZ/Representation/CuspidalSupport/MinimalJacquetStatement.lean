import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.CuspidalSupport.MinimalJacquetStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.MinimalJacquetStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.MinimalJacquetStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding MinimalNonzeroJacquetTheorem
open Langlands.GeneralLinear
universe uF uV

/-- Every nonzero smooth representation of an actual p-adic general linear
 group has a nonzero quasicuspidal normalized Jacquet module for some standard
 block parabolic. All natural ranks, including zero, are included. -/
def MinimalNonzeroJacquetTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    letI := T.generalLinearTopology n
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      Nontrivial A → ∃ B : BlockShape n,
        let J := (T.normalizedJacquetFunctor B).obj A
        Nontrivial J ∧ IsLeviQuasicuspidal B J.representation

end Langlands.AllFieldBZ.CuspidalSupport
