import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.GroupScheme.SimplyConnected.Basic

/-!
# Simply connected normalizer facet stabilizers fix their facets pointwise

A source-derived prerequisite for the simply connected part of AS 5.
This module states a proposition and supplies no proof of it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

/-- For full omega-compatible valuation data of a semisimple simply connected
group over a nonarchimedean local field, a normalizer element stabilizing a
facet of the apartment fixes that facet pointwise. Derived from KP 9.3.26
using the apartment, root and facet comparisons of KP 6.2.6, 9.6.5–6 and
9.4.31. -/
def SimplyConnectedFacetFixingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G),
    IsSimplyConnected G →
    ∀ (Fa : Set B.Apartment),
      AffineRootSystem.IsFacet B.affineRoots Fa →
      ∀ (n : normalizerPoints B.i),
        (fun x : B.Apartment => n • x) '' Fa = Fa →
        ∀ x ∈ Fa, n • x = x

end Langlands.Geometry.Building
