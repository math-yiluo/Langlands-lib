/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeComparison
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeFinal

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

/-- (blueprint: lem-sc-cartesian-chart-raw-adjunction-pullback) -/
lemma chartRawAdj_classPullback {S X B T T' : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (wg' : g' = a ≫ g)
    (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (g'' : T' ⟶ S) (wg'' : g'' = a' ≫ g) (wb : g'' = b ≫ g')
    (l : pullback a' (pullback.snd f g) ⟶ pullback a (pullback.snd f g))
    (hl₁ : l ≫ pullback.fst a (pullback.snd f g) =
      pullback.fst a' (pullback.snd f g) ≫ b)
    (hl₂ : l ≫ pullback.snd a (pullback.snd f g) = pullback.snd a' (pullback.snd f g))
    (hw : l ≫ (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) =
      pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (V : B.Etale)
    (U : T'.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a')
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V))
    (z' : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a' (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V))
    (hz' : z' = abelianHigherDirectImageRawPullback l
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g)
      (pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g) hw n _ _
      ((upperStarComp AddCommGrpCat.{u + 1} l
        (pullback.snd a (pullback.snd f g)) (pullback.snd a' (pullback.snd f g))
        hl₂.symm).inv.app (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)) V z) :
    cartesianChartClassPullback a b a' ha V U r hr _ (n : ℤ)
      ((cartesianChartRawAdjunctionIso f g a g' wg' F n V).hom z) ≫
      (shiftFunctor _ (n : ℤ)).map
        (cartesianDerivedImageMap f g' g'' b wb
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
    (DerivedCategory.Plus.singleFunctor _ 0).map
      (abelianFreeRepresentablePullbackSquareIso a' V U r hr).hom ≫
      (cartesianChartRawAdjunctionIso f g a' g'' wg'' F n V).hom z' := by
  apply chartClassPullback_postcomp
  exact chartRawAdj_pullback f g a g' wg' b a' ha g'' wg'' wb l hl₁ hl₂ hw F n V z z' hz'

end AlgebraicGeometry.Etale
