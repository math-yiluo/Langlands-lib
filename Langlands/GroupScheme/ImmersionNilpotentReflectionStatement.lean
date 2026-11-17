import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Statement: immersions are reflected by a nilpotent thickening -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A morphism of schemes over `Spec A` is an immersion if its base change to `Spec (A/J)`
is an immersion, for a nilpotent ideal `J`. No flatness assumption is needed. This is the
scheme-theoretic step used in SGA 3, IX, the proof of Theorem 3.6 bis (a). -/
def ImmersionNilpotentReflectionStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (X Y : Over (Spec (CommRingCat.of A))) (f : X ⟶ Y),
      IsImmersion (((Over.pullback (Spec.algebraMap A (A ⧸ J))).map f).left) →
        IsImmersion f.left

end Langlands.GroupScheme
