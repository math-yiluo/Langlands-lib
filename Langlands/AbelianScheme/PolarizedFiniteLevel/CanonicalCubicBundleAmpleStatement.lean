import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle

/-! # Ampleness of the canonical diagonal bundle and its cube over a field -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The actual canonical diagonal bundle and its actual tensor cube are ample for
every ordinary polarized datum over a field. This proposition is a statement target. -/
def CanonicalCubicBundleAmpleStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] (g d n : ℕ)
    (a : Datum P (Spec (CommRingCat.of K)) g d n),
    a.canonicalBundle.IsAmple ∧ a.cubicBundle.IsAmple

end Langlands.AbelianScheme.PolarizedFiniteLevel
