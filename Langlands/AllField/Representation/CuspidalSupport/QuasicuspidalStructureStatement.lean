import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Langlands.AllField.Group.GL.PadicBlocks
/-! The quasicuspidal structure prerequisites of BZ77 section 2.4. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviQuasicuspidalDecompositionTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n)

/-- A smooth representation splits into complementary actual invariant
subspaces, one quasicuspidal and the other with no nonzero quasicuspidal
subquotient. `IsCompl` asserts both zero intersection and full sum. -/
def LeviQuasicuspidalDecompositionTheorem : Prop :=
  letI := T.topology
  ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
    ∃ S Q : Subrepresentation A.representation,
      IsCompl S.toSubmodule Q.toSubmodule ∧
      IsLeviQuasicuspidal B (SmoothRep.subrepresentation A S).representation ∧
      ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
        SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q) →
        IsLeviQuasicuspidal B D.representation → Subsingleton D

end Langlands.AllField.CuspidalSupport
