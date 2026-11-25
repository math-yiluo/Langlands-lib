/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeTransport
-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true

private theorem cartesianChartAdjunct_spec {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (pullback.snd f g')).derivedPlus.homEquiv _ _
        ((cartesianChartAdjunctIso f g a g' w F q V).hom z) ≫
          (R+((pullback.snd f g')_*[AddCommGrpCat.{u + 1}]).commShiftIso
            (q : ℤ)).hom.app _ =
      (cartesianChartRawAdjunctionIso f g a g' w F q V).hom z := by
  rfl

/-- (blueprint: lem-sc-cartesian-chart-cohomology-evaluation) -/
private theorem chartCohomologyIso_eval {S X B T : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (V : B.Etale) (U : T.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)) :
    (cartesianChartCohomologyIso f g a g' w F n V U r hr).hom
      (rawRestrictedCohomologyComparison _ n _ V z) =
    (DerivedCategory.Plus.singleFunctor _ 0).map
        (abelianFreeRepresentablePullbackSquareIso a V U r hr).hom ≫
      (cartesianChartRawAdjunctionIso f g a g' w F n V).hom z := by
  dsimp only [cartesianChartCohomologyIso]
  erw [add_iso_trans_apply, add_iso_trans_apply]
  simp only [Iso.symm_hom]
  erw [Iso.hom_inv_id_apply]
  erw [yoneda_mapIso_apply]
  rfl

end AlgebraicGeometry.Etale
