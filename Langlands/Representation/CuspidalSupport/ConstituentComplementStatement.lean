import Langlands.Representation.Category.Subquotients

/-!
# Constituent transfer through complementary invariant subspaces

This proposition bundles two elementary transfers of actual constituents
between a smooth representation and one of two complementary invariant
subspaces.
-/

namespace Langlands.CuspidalSupport

universe uR uG uV

/-- Occurrence of an irreducible subquotient in one complementary summand when
it does not occur in the other, and transfer of actual embeddings and quotient
maps from a complementary summand to the ambient representation, with
independent coefficient, group, and representation-carrier universes. -/
def ComplementConstituentTransferTheorem : Prop :=
  (∀ {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
      {A D : SmoothRep.{uR, uG, uV} R G}
      (S Q : Subrepresentation A.representation),
    IsCompl S.toSubmodule Q.toSubmodule → D.IsIrreducible →
    SmoothRep.IsSubquotient D A →
    ¬ SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q) →
    SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A S)) ∧
  (∀ {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
      {A D : SmoothRep.{uR, uG, uV} R G}
      (S Q : Subrepresentation A.representation),
    IsCompl S.toSubmodule Q.toSubmodule →
    SmoothRep.IsSubrepresentation D (SmoothRep.subrepresentation A S) ∧
      SmoothRep.IsQuotient D (SmoothRep.subrepresentation A S) →
    SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A)

end Langlands.CuspidalSupport
