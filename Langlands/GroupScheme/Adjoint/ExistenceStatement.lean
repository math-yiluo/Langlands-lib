import Langlands.GroupScheme.Adjoint.Quotient

/-! # Statement: existence of the actual adjoint quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive group over a field has an actual adjoint quotient by its
full scheme-theoretic centre (Milne, Corollary 17.62(e) and Remark 17.63; CGP A.1.10–A.1.12). -/
def AdjointQuotientExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∃ (A : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ A), IsAdjointQuotient q

end Langlands.GroupScheme
