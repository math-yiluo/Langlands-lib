import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Algebraic boundedness of actual affine rational points

This is the regular-function definition of KP 2.2.1, expressed without choosing
a numerical representative of the valuation. It makes no compactness assertion.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F]
variable (X : Over (Spec (CommRingCat.of F))) [IsAffine X.left]

/-- Evaluation of actual global regular functions at an identity-test rational
point, using the published scheme-point / algebra-point equivalence. -/
def rationalPointAlgebraHom (p : RationalPoint F X) :
    AffineCoordinateRing F X →ₐ[F] F :=
  (affineSchemePointEquiv F X F (rationalPointEquiv F X p)).toAlgHom

/-- KP algebraic boundedness: each regular function has a uniform valuative
upper bound on the set, or equivalently a finite additive-valuation lower bound.
The nonzero bound includes zero function values. No topology is assumed. -/
def IsAlgebraicallyBounded [ValuativeRel F] (B : Set (RationalPoint F X)) : Prop :=
  ∀ f : AffineCoordinateRing F X,
    ∃ b : F, b ≠ 0 ∧ ∀ p ∈ B, rationalPointAlgebraHom F X p f ≤ᵥ b

end Langlands.AlgebraicGeometry.PointTopology
