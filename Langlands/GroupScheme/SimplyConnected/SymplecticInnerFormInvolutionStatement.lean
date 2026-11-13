import Langlands.GroupScheme.SymplecticInnerForm.InvolutionModel
import Langlands.GroupScheme.Rational.QuasiSplitInnerForm
import Langlands.GroupScheme.Symplectic.Basic

/-! # Descent of a symplectic inner form to a central simple algebra with involution -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An inner form of `Sp_{2n}` is the reduced-norm-one isometry group of a central
simple algebra of degree `2n`, with an actual finite Galois standard symplectic
splitting chart for its involution. -/
def SymplecticInnerFormInvolutionStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ)
    (q : QuasiSplitInnerForm G),
    2 ≤ n → Nonempty (q.model ≅ Symplectic.groupScheme K n) →
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A)
        (_ : Algebra.IsCentral K A) (_ : IsSimpleRing A) (_ : FiniteDimensional K A),
        Langlands.CentralSimple.reducedDegree K A = 2 * n ∧
          ∃ τ : Quaternionic.FirstKindInvolution K A,
            SymplecticInnerForm.HasStandardSymplecticSplitting τ n ∧
              Nonempty (G ≅ SymplecticInnerForm.normOneGroup τ)

end Langlands.GroupScheme
