/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The map from the free sheaf of the inverse-image open to the inverse image of
its free sheaf. It classifies the pullback of the identity section, via the unit
of inverse image/direct image and restriction along `openSectionPullback`.
Source: Stacks Project, Tags 03F3 and 0A50; free-abelian Yoneda adjunction.
(blueprint: def-weil-pbc-etale-open-free-sheaf-pullback) -/
noncomputable def etaleOpenFreeSheafPullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (W : X.Opens) :
    (etaleOpenFreeSheaf Y).obj (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) ⟶
      (upperStar AddCommGrpCat.{u + 1} g).obj
        ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)) := by
  let A := (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)
  let F := (upperStar AddCommGrpCat.{u + 1} g).obj A
  let s := EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
    (Scheme.Etale.mk W.ι) A (𝟙 A)
  exact (EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
    (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) F).symm
      (F.obj.map (openSectionPullback g W).op
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app A).hom.app
          (op (Scheme.Etale.mk W.ι)) s))

end AlgebraicGeometry.Etale
