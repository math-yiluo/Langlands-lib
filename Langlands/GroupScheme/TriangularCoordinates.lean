import Langlands.GroupScheme.AffinePointTopology
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Triangular polynomial coordinates on affine group schemes over a field

`HasTriangularCoordinates U` says that the coordinate ring of an affine group scheme `U` over
a field `F` is a polynomial ring in global functions `t₁, …, t_d`. In these coordinates the
group law on the points over every `F`-algebra must have the triangular form
`(x * y)_i = x_i + y_i + P_i(x_j, y_j : j < i)`. `UnipotentTriangularCoordinatesStatement`
asserts that every smooth connected unipotent affine group scheme of finite type over a field
of characteristic zero has such coordinates. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Triangular polynomial coordinates on an affine group scheme `U` over a field `F`. The
global functions `t : Fin d → 𝒪(U)` identify the coordinate ring with the polynomial ring
`F[X₀, …, X_{d-1}]`. For every `F`-algebra `A`, all points `x y ∈ U(A)` and every index `i`,
the `i`-th coordinate of `x * y` is `x_i + y_i + P_i(x, y)`. The polynomial `P_i` (variables
`Sum.inl j` for `x_j` and `Sum.inr j` for `y_j`) involves only indices `j < i`. -/
def HasTriangularCoordinates {F : Type u} [Field F]
    (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left] : Prop :=
  ∃ (d : ℕ) (t : Fin d → AffineCoordinateRing F U.X)
    (P : Fin d → MvPolynomial (Fin d ⊕ Fin d) F),
    Function.Bijective
        (MvPolynomial.aeval t : MvPolynomial (Fin d) F →ₐ[F] AffineCoordinateRing F U.X) ∧
      (∀ i, ∀ v ∈ (P i).vars, Sum.elim id id v < i) ∧
      ∀ (A : CommAlgCat.{u} F) (x y : U.affinePoints A) (i : Fin d),
        U.affinePointEvaluation A (x * y) (t i) =
          U.affinePointEvaluation A x (t i) + U.affinePointEvaluation A y (t i) +
            MvPolynomial.aeval
              (Sum.elim (fun j => U.affinePointEvaluation A x (t j))
                (fun j => U.affinePointEvaluation A y (t j))) (P i)

/-- **Triangular coordinates on unipotent groups in characteristic zero.** Every smooth
connected unipotent affine group scheme of finite type over a field of characteristic zero
has triangular polynomial coordinates. -/
def UnipotentTriangularCoordinatesStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom],
    Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U → HasTriangularCoordinates U

end Langlands.GroupScheme
