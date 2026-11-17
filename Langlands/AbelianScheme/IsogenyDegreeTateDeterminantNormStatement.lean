import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.Tate.RationalPrimeHom
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # The `p`-adic absolute value of the degree of an endomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Let `A` be an abelian scheme over an algebraically closed field `k` of characteristic
zero and let `p` be a prime. For every actual isogeny `α : A ⟶ A`, the `p`-adic absolute
value of its degree equals the `p`-adic absolute value of the determinant of its actual
rational `p`-adic Tate map, and for every actual endomorphism that is not an isogeny, that
determinant is `0`. The degree is the rank of the finite flat underlying morphism at a point
of `A` (Milne, *Abelian Varieties*, the displayed computation in the proof of
Proposition 12.9). This proposition is a statement target, not a proof. -/
def IsogenyDegreeTateDeterminantNormStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] (α : A ⟶ A),
      (IsIsogeny α → ∀ y : A.X.left,
        ‖((hom α).finrank y : ℚ_[p])‖ =
          ‖LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α)‖) ∧
      (¬ IsIsogeny α →
        LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α) = 0)

end Langlands.AbelianScheme
