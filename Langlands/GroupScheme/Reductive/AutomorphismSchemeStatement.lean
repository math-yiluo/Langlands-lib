import Langlands.GroupScheme.AutomorphismSchemeInnerLocus
import Langlands.GroupScheme.Reductive.InnerActionLocusStatement

/-! # Full automorphism group schemes with a clopen adjoint subgroup -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The portion of Conrad, Theorem 7.1.9(1), needed for arbitrary inner-action
loci: full all-test automorphism representability and a clopen natural adjoint
subgroup, including the empty-base case. -/
def ReductiveAutomorphismSchemeStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ I : GroupAutomorphismScheme G,
      ∀ (Gad : GroupScheme S) (p : G ⟶ Gad),
        RelativeRoot.IsFppfQuotient (center G) p →
      ∀ c : AutomorphicAction Gad G,
        c.restrict p = AutomorphicAction.conjugation (𝟙 G) →
        IsOpenImmersion (I.classifyAction c).hom.hom.left ∧
          IsClosedImmersion (I.classifyAction c).hom.hom.left

/-- Full automorphism representability with a clopen adjoint subgroup supplies
the universal clopen inner part of every action. -/
theorem reductiveInnerActionLocus_of_automorphismScheme
    (h : ReductiveAutomorphismSchemeStatement.{u}) :
    ReductiveInnerActionLocusStatement.{u} := by
  intro S G H hG Gad p hp c hc a
  obtain ⟨I, hI⟩ := h S G hG
  obtain ⟨hco, hcc⟩ := hI Gad p hp c hc
  exact I.exists_innerActionLocus a c hco hcc

end Langlands.GroupScheme
