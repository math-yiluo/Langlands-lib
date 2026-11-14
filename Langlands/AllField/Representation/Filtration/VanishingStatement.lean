import Langlands.Representation.Filtration.VanishingStatement
import Langlands.AllField.Group.GL.PadicBlocksSupplement
/-! Internal finite-filtration criteria used in BZ77 2.13(a),(b). -/

namespace Langlands.AllField

universe uR uG uV uF

namespace CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

/-- Absence of nonzero quasicuspidal smooth subquotients propagates from
smooth representatives of all actual graded quotients to the ambient module.
The field and carrier universes are independent; no positivity or finiteness
condition on the rank or the smooth representations is imposed. -/
def PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n)
      (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F))
      (r : ℕ) (s : ObjectRepFiltration (Rep.of A.representation) r),
      (∀ i : Fin r,
        ∃ Q : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
          Nonempty ((s.gradedRepresentation i).ρ.Equiv Q.representation) ∧
          ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
            SmoothRep.IsSubquotient D Q →
            IsLeviQuasicuspidal B D.representation → Subsingleton D) →
      ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
        SmoothRep.IsSubquotient D A →
        IsLeviQuasicuspidal B D.representation → Subsingleton D

end CuspidalSupport

end Langlands.AllField
