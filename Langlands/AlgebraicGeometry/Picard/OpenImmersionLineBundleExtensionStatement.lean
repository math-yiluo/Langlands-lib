import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # Extension of line bundles across an open immersion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A line bundle on an open subscheme extends if the target is locally
Noetherian and its stalks outside that open are factorial. This defines the
proposition; it does not prove it. -/
def OpenImmersionLineBundleExtensionStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (Y : Scheme.{u})
    (j : Y ⟶ X) [IsOpenImmersion j],
    (∀ x : X, x ∉ Set.range j →
      UniqueFactorizationMonoid (X.presheaf.stalk x)) →
    ∀ D : LineBundle Y,
      ∃ E : LineBundle X,
        Nonempty (((LineBundle.pullback j).obj E).obj ≅ D.obj)

end Langlands.AlgebraicGeometry.Picard
