import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.AffineWeylGroups

/-!
# Simply connected normalizer image over the maximal unramified extension

This is the simply connected assertion of corrected KP AS 5, specialized to
the actual maximal unramified field and arbitrary supplied building data.
It is a proposition definition, not a proof.
-/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

/-- For a simply connected group over the actual maximal unramified extension,
the image of the original normalizer action on any supplied omega-compatible
apartment is exactly the affine Weyl group of its affine roots. This is derived
from KP Proposition 9.4.35 by the apartment and root comparison of 9.6.5–6
and uniqueness in Proposition 6.2.6. -/
def SimplyConnectedNormalizerAffineWeylStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∀ C : BuildingData F G,
      C.apartment.normalizerAffineEquiv.range =
        AffineRootSystem.affineWeylGroup C.affineRoots

end Langlands.Geometry.Building.MaximalUnramified
