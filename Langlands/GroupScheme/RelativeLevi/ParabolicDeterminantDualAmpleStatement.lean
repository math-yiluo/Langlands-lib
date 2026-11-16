import Langlands.GroupScheme.RelativeLevi.ParabolicFiniteQuotientChart
import Langlands.GroupScheme.RelativeLevi.ParabolicLieDeterminant
import Langlands.AlgebraicGeometry.Picard.LineBundleDualSectionEvaluation
import Langlands.AlgebraicGeometry.Picard.Ample

/-! # Statement: ampleness of the actual parabolic Lie determinant dual -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open ParabolicSubgroupModuli

/-- The dual determinant of the actual universal conjugate parabolic is ample
on every finite coproduct of affine-base parabolic quotient schemes.
This is the local positivity input from Conrad (2014), Theorem 2.3.6(2),
pp.72–75, and the proof of Corollary 5.2.9, p.157. -/
def FiniteAffineParabolicDeterminantDualAmpleStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (I : Type u) [Finite I] (P : I → GroupScheme (Spec (CommRingCat.of R)))
    (j : ∀ a, P a ⟶ G) (hj : ∀ a, IsRelativeParabolicSubgroup (j a)),
    (parabolicRepresentative (finiteAffineParabolicFamily hG j hj)).lieDeterminant.dual.IsAmple

end Langlands.GroupScheme
