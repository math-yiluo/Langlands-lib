import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.Tate.RationalPrimeHom
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # Degree of an endomorphism as a rational Tate determinant -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Let `A` be an abelian scheme over an algebraically closed field `k` and let `p` be a
prime different from the characteristic of `k`. For every actual endomorphism `α` of `A`,
the degree of `α` is the determinant of the actual rational `p`-adic Tate map of `α`. Here
the degree of an isogeny is the rank of its finite flat underlying morphism at a point of
`A`, and the degree of an endomorphism that is not an isogeny is `0`
(Milne, *Abelian Varieties*, p. 21 and Proposition 12.9).
This proposition is a statement target, not a proof. -/
def IsogenyDegreeTateDeterminantStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime], (p : k) ≠ 0 →
    ∀ α : A ⟶ A,
      (IsIsogeny α → ∀ y : A.X.left,
        ((hom α).finrank y : ℚ_[p]) =
          LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α)) ∧
      (¬ IsIsogeny α →
        LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α) = 0)

end Langlands.AbelianScheme
