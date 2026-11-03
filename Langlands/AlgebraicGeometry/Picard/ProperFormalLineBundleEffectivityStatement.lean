import Langlands.AlgebraicGeometry.Picard.FormalLineBundleSystem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-! # Proper formal line-bundle effectivity over complete local rings: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Every compatible system of actual line bundles on the maximal-ideal
thickenings of a proper scheme over a complete local noetherian ring has an
actual line-bundle algebraization with a transition-compatible comparison. -/
def ProperFormalLineBundleEffectivityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)), IsProper f →
      ∀ F : FormalLineBundleSystem f (IsLocalRing.maximalIdeal R),
        ∃ L : LineBundle X, FormalLineBundleSystem.IsAlgebraization L F

end Langlands.AlgebraicGeometry.Picard
