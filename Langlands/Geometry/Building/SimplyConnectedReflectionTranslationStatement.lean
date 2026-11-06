import Langlands.Geometry.Building.ReflectionTranslationLattice
import Langlands.GroupScheme.SimplyConnected.Basic

/-!
# Simply connected realization of actual centralizer translations

An internal structural proof obligation for the direct facet-fixing route.
This module states a proposition and supplies no proof of it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

/-- For the supplied full omega-compatible valuation data of a semisimple
simply connected group, every actual reduced centralizer translation is
realized by a centralizing product of actual reflection representatives. -/
def SimplyConnectedReflectionTranslationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G),
    IsSimplyConnected G →
      B.reflectionTranslationLattice = B.centralizerTranslationLattice

end Langlands.Geometry.Building
