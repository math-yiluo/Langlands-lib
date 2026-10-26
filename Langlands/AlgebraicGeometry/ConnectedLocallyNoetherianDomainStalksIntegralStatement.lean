import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties

/-! # Integrality from connectedness, local Noetherianity, and domain stalks -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A connected locally Noetherian scheme whose stalks are domains is integral. -/
def ConnectedLocallyNoetherianDomainStalksIntegral : Prop :=
  ∀ (X : Scheme.{u}), IsLocallyNoetherian X → ConnectedSpace X →
    (∀ x : X, IsDomain (X.presheaf.stalk x)) → IsIntegral X

end Langlands.AlgebraicGeometry
