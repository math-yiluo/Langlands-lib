import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.Representation.Filtration.VanishingStatement

/-!
# All-field port of `Langlands.Representation.Filtration.VanishingStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Filtration.VanishingStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
universe uR uG uV uF

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement
open Langlands.GeneralLinear
/-- Absence of nonzero quasicuspidal smooth subquotients propagates from
smooth representatives of all actual graded quotients to the ambient module.
The field and carrier universes are independent; no positivity or finiteness
condition on the rank or the smooth representations is imposed. -/
def PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n)
      (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (r : ℕ) (s : ObjectRepFiltration (Rep.of A.representation) r),
      (∀ i : Fin r,
        ∃ Q : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
          Nonempty ((s.gradedRepresentation i).ρ.Equiv Q.representation) ∧
          ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
            SmoothRep.IsSubquotient D Q →
            IsLeviQuasicuspidal B D.representation → Subsingleton D) →
      ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        SmoothRep.IsSubquotient D A →
        IsLeviQuasicuspidal B D.representation → Subsingleton D

end CuspidalSupport
end Langlands.AllFieldBZ
