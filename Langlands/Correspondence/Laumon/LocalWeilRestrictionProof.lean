import Langlands.Correspondence.Laumon.UnramifiedLines
import Langlands.Correspondence.HenniartLadicDenseRestriction
import Langlands.Weil.Local.SepClosedTopology

/-!
# Restriction to the local Weil group of `k((t))`: proof

This module proves `LocalWeilRestrictionStatement`: the projection `localProjection` of the
Library's local Weil group of `LaurentSeries k` to the absolute Galois group has dense image
(`localProjection_denseRange`), and restriction along a homomorphism with dense image
preserves and reflects intertwiners, isomorphism, irreducibility and finite models of
continuous ℓ-adic representations (`ladicRestriction_of_denseRange`).
-/

universe u uW

namespace Langlands.Henniart.Laumon

open Langlands.Henniart.LocalNumerical Langlands.Weil.Local.SepClosed

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

/-- **Restriction to the local Weil group.** `LocalWeilRestrictionStatement` holds. -/
theorem localWeilRestriction : LocalWeilRestrictionStatement.{u, uW} := by
  intro k _ _ ℓ _ A B hA hB
  exact ladicRestriction_of_denseRange ℓ
    (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k))).toMonoidHom
    (localProjection_denseRange (LaurentSeries k) (SeparableClosure (LaurentSeries k))) A B hA hB

end Langlands.Henniart.Laumon
