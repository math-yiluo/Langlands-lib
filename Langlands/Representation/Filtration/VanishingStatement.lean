import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Group.GL.PadicBlocks

/-! Internal finite-filtration criteria used in BZ77 2.13(a),(b). -/

namespace Langlands

universe uR uG uV uF

/-- A finite zero-to-full filtration with zero actual graded quotients
has zero ambient representation. Repeated steps and length zero are allowed. -/
def ObjectRepFiltrationSubsingletonStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Monoid G]
    (A : Rep.{uV} R G) (r : ℕ) (s : ObjectRepFiltration A r),
    (∀ i : Fin r, Subsingleton (s.gradedRepresentation i)) → Subsingleton A

namespace CuspidalSupport

open GeneralLinear

/-- Absence of nonzero quasicuspidal smooth subquotients propagates from
smooth representatives of all actual graded quotients to the ambient module.
The field and carrier universes are independent; no positivity or finiteness
condition on the rank or the smooth representations is imposed. -/
def PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
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

end Langlands
