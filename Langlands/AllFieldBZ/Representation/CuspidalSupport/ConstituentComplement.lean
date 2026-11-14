import Langlands.AllFieldBZ.Representation.Category.ConstituentDichotomy
import Langlands.Representation.CuspidalSupport.ConstituentComplement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.ConstituentComplement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.ConstituentComplement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport
open CategoryTheory
universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
  {A D : SmoothRep.{uR, uG, uV} R G}

/-- Inclusion followed by the quotient identifies one complement with the
quotient by the other. -/
private def _root_.Langlands.CuspidalSupport.complementQuotientIso (S Q : Subrepresentation A.representation)
    (hSQ : IsCompl S.toSubmodule Q.toSubmodule) :
    SmoothRep.subrepresentation A Q ≅ SmoothRep.quotient A S :=
  SmoothRep.mkIso <| Representation.Equiv.mk
    (S.toSubmodule.quotientEquivOfIsCompl Q.toSubmodule hSQ).symm
    fun g => by
      exact (SmoothRep.hom (SmoothRep.subtype A Q ≫ SmoothRep.mkQ A S)).isIntertwining' g

end Langlands.AllFieldBZ.CuspidalSupport
