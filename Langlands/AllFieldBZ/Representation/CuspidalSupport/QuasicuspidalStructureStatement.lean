import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviCuspidalConstituentTheorem LeviQuasicuspidalDecompositionTheorem
open Langlands.GeneralLinear
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- A smooth representation splits into complementary actual invariant
subspaces, one quasicuspidal and the other with no nonzero quasicuspidal
subquotient. `IsCompl` asserts both zero intersection and full sum. -/
def LeviQuasicuspidalDecompositionTheorem : Prop :=
  letI := T.topology
  ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    ∃ S Q : Subrepresentation A.representation,
      IsCompl S.toSubmodule Q.toSubmodule ∧
      IsLeviQuasicuspidal B (SmoothRep.subrepresentation A S).representation ∧
      ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q) →
        IsLeviQuasicuspidal B D.representation → Subsingleton D

/-- An irreducible cuspidal constituent of an admissible representation
occurs both as an actual subrepresentation and as an actual quotient. -/
def LeviCuspidalConstituentTheorem : Prop :=
  letI := T.topology
  ∀ A D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    A.IsAdmissible → D.IsIrreducible → IsLeviCuspidal B D.representation →
    SmoothRep.IsSubquotient D A →
      SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A

end Langlands.AllFieldBZ.CuspidalSupport
