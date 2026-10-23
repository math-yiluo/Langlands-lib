import Langlands.Representation.CuspidalSupport.ConstituentComplementStatement
import Langlands.Representation.Category.ConstituentDichotomy
import Mathlib.LinearAlgebra.Projection

/-! Transfer of actual constituent maps through complementary invariant subspaces. -/

noncomputable section

namespace Langlands.CuspidalSupport

open CategoryTheory

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
  {A D : SmoothRep.{uR, uG, uV} R G}

/-- Inclusion followed by the quotient identifies one complement with the
quotient by the other. -/
private def complementQuotientIso (S Q : Subrepresentation A.representation)
    (hSQ : IsCompl S.toSubmodule Q.toSubmodule) :
    SmoothRep.subrepresentation A Q ≅ SmoothRep.quotient A S :=
  SmoothRep.mkIso <| Representation.Equiv.mk
    (S.toSubmodule.quotientEquivOfIsCompl Q.toSubmodule hSQ).symm
    fun g => by
      exact (SmoothRep.hom (SmoothRep.subtype A Q ≫ SmoothRep.mkQ A S)).isIntertwining' g

/-- If an irreducible constituent does not occur in one complementary summand,
it occurs in the other. -/
theorem irreducibleSubquotient_of_isCompl
    (S Q : Subrepresentation A.representation)
    (hSQ : IsCompl S.toSubmodule Q.toSubmodule) (hD : D.IsIrreducible)
    (h : SmoothRep.IsSubquotient D A)
    (hQ : ¬ SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q)) :
    SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A S) := by
  rcases SmoothRep.irreducibleSubquotient_dichotomy hD h S with hS | hS
  · exact hS
  · exact False.elim (hQ (hS.of_iso_right (complementQuotientIso S Q hSQ).symm))

/-- Actual embeddings and quotient maps for one complementary summand give
actual embeddings and quotient maps for the ambient representation. -/
theorem constituent_of_isCompl
    (S Q : Subrepresentation A.representation)
    (hSQ : IsCompl S.toSubmodule Q.toSubmodule)
    (hS : SmoothRep.IsSubrepresentation D (SmoothRep.subrepresentation A S) ∧
      SmoothRep.IsQuotient D (SmoothRep.subrepresentation A S)) :
    SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A := by
  obtain ⟨⟨i, hi⟩, ⟨q, hq⟩⟩ := hS
  constructor
  · refine ⟨i ≫ SmoothRep.subtype A S, ?_⟩
    exact (SmoothRep.subtype_injective A S).comp hi
  · let e := complementQuotientIso Q S hSQ.symm
    refine ⟨SmoothRep.mkQ A Q ≫ e.inv ≫ q, ?_⟩
    exact hq.comp ((SmoothRep.hom_hom_surjective e.symm).comp (SmoothRep.mkQ_surjective A Q))

/-- The exact published constituent transfer theorem for complementary invariant
subspaces, with independent coefficient, group, and carrier universes. -/
theorem complementConstituentTransfer :
    ComplementConstituentTransferTheorem.{uR, uG, uV} := by
  constructor
  · exact irreducibleSubquotient_of_isCompl
  · exact constituent_of_isCompl

end Langlands.CuspidalSupport
