import Langlands.Representation.Category.Subquotients
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.Complex.Basic

namespace Langlands.CuspidalSupport

universe uG uV

/-- The fixed-vector induction underlying the cuspidal constituent argument.
All subgroup and representation hypotheses are concrete, and only the selected
fixed-vector space of the ambient representation is finite dimensional. -/
def FixedVectorConstituentInduction : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.Normal] [(H ⊔ Subgroup.center G).FiniteIndex]
    (K : OpenSubgroup G), IsCompact (K : Set G) → K.toSubgroup ≤ H →
    ∀ (A D : SmoothRep.{0, uG, uV} ℂ G),
      Representation.IsSemisimpleRepresentation (A.representation.comp H.subtype) →
      (∀ S : Subrepresentation (A.representation.comp H.subtype),
        fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤) →
      Module.Finite ℂ (fixedVectors A.representation K.toSubgroup) →
      D.IsAdmissible → D.IsIrreducible →
      Nontrivial (fixedVectors D.representation K.toSubgroup) →
      SmoothRep.IsSubquotient D A →
      SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A

end Langlands.CuspidalSupport
