import Langlands.Weil.Representation.Twist
import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.OperationClosureProof
import Langlands.Representation.Twist.AlgebraProof
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Shared properties of scalar character twists

Common finite-representation helpers used by both genuine class twists and
exact virtual twists. The four declarations retain their published names.
-/

noncomputable section

universe uK uG

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- Twisting retains the underlying vector space and hence its rank. -/
@[simp]
theorem rank_twist (χ : G →* Kˣ) (A : FiniteRepresentation K G) :
    (twist χ A).rank = A.rank := rfl

/-- The identity character gives an actual representation equivalence. -/
def twistOneEquiv (A : FiniteRepresentation K G) : Equiv (twist 1 A) A := by
  change (Langlands.twist 1 A.representation).Equiv A.representation
  rw [Langlands.twist_one]
  exact Representation.Equiv.refl _

/-- Iterated twists agree with multiplication of the actual characters. -/
def twistMulEquiv (χ η : G →* Kˣ) (A : FiniteRepresentation K G) :
    Equiv (twist χ (twist η A)) (twist (χ * η) A) := by
  change (Langlands.twist χ (Langlands.twist η A.representation)).Equiv
    (Langlands.twist (χ * η) A.representation)
  rw [Langlands.twist_twist]
  exact Representation.Equiv.refl _

/-- Continuous characters preserve the published usual-topology continuity
predicate, using the published continuous scalar-twist theorem. -/
theorem isContinuous_twist [TopologicalSpace G] (χ : G →ₜ* ℂˣ)
    {A : FiniteRepresentation ℂ G} (hA : A.IsContinuous) :
    (twist χ.toMonoidHom A).IsContinuous :=
  Weil.OperationClosure.continuous_twist χ.toMonoidHom A.representation χ.continuous hA

end Langlands.FiniteRepresentation
