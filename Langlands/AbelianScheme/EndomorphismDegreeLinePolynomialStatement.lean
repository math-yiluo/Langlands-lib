import Langlands.AbelianScheme.IsogenySpecialization
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Degrees of endomorphisms along lines are polynomial -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Let `A` be an abelian scheme of relative dimension `g` over an algebraically closed field
`k`. There is a rational-valued function `δ` on the actual endomorphisms of `A` that equals
the degree on isogenies and is polynomial of degree at most `2 * g` along every line: for all
endomorphisms `φ` and `ψ`, the function `n ↦ δ (n • φ + ψ)` on natural numbers is given by a
rational polynomial of natural degree at most `2 * g`. The degree of an isogeny is the rank of
its finite flat underlying morphism at a point of `A`. This is a form of Milne,
*Abelian Varieties*, Proposition 12.4 and the reduction at the start of its proof. Unlike
Milne's degree, `δ` is not required to vanish on endomorphisms that are not isogenies. This
proposition is a statement target, not a proof. -/
def EndomorphismDegreeLinePolynomialStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (g : ℕ), A.HasRelativeDimension g →
      ∃ δ : (A ⟶ A) → ℚ,
        (∀ β : A ⟶ A, IsIsogeny β → ∀ y : A.X.left, δ β = ((hom β).finrank y : ℚ)) ∧
        ∀ φ ψ : A ⟶ A, ∃ R : Polynomial ℚ, R.natDegree ≤ 2 * g ∧
          ∀ n : ℕ, δ (n • φ + ψ) = R.eval (n : ℚ)

end Langlands.AbelianScheme
