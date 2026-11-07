import Langlands.GroupScheme.Rational.RootActionWeights
import Langlands.GroupScheme.Rational.RepresentationNormalizerWeights

/-! # Degree-one root action on a reflected highest-weight line -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

/-- Over an algebraically closed field of any characteristic, a simple-root
coefficient of degree one acts nontrivially on the reflection of a highest-weight
line when the highest weight has simple-coroot pairing one. -/
def SplitSimpleRootHighestCoefficientNonvanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (d : ℕ) (ρ : MatrixRepresentation G (Fin d))
    (lam : characterLattice p.torus), p.IsHighestWeight ρ lam →
    ∀ (a : p.base.support),
      p.rootDatum.toLinearMap lam (p.rootDatum.coroot a) = 1 →
    ∀ (x : p.NormalizedRootParametrization a) (s : p.SimpleReflectionRepresentative a)
      (v : Fin d → k), v ∈ p.representationWeightSpace ρ lam → v ≠ 0 →
        MatrixRepresentation.AdditiveDividedPowers.coefficientMatrix (ρ.restrict x.hom) 1 *ᵥ
          ((ρ.rationalMatrix s.point : Matrix (Fin d) (Fin d) k) *ᵥ v) ≠ 0

end Langlands.GroupScheme
