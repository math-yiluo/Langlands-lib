/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeAdjunction
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeTransport
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeEvaluation
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true

private theorem chartRawAdj_pullback {S X B T T' : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (g'' : T' ⟶ S) (w' : g'' = a' ≫ g) (wb : g'' = b ≫ g')
    (l : pullback a' (pullback.snd f g) ⟶ pullback a (pullback.snd f g))
    (hl₁ : l ≫ pullback.fst a (pullback.snd f g) =
      pullback.fst a' (pullback.snd f g) ≫ b)
    (hl₂ : l ≫ pullback.snd a (pullback.snd f g) = pullback.snd a' (pullback.snd f g))
    (hw : l ≫ (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) =
      pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (V : B.Etale)
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
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a a' ha).hom.app
          ((abelianComparisonFree B).obj V)) ≫
      (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
        (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ≫
      (D+((b)^*[AddCommGrpCat.{u + 1}])).map
        ((cartesianChartRawAdjunctionIso f g a g' w F n V).hom z) ≫
      (D+((b)^*[AddCommGrpCat.{u + 1}]).commShiftIso (n : ℤ)).hom.app _ ≫
      (shiftFunctor _ (n : ℤ)).map
        (cartesianDerivedImageMap f g' g'' b wb
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
    (cartesianChartRawAdjunctionIso f g a' g'' w' F n V).hom z' := by
  subst z'
  let t := cartesianImageProjection f g' g'' b wb
  let sq : CommSq t (pullback.snd f g'') (pullback.snd f g') b :=
    ⟨cartesianImageProjection_snd f g' g'' b wb⟩
  let adj := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (pullback.snd f g')).derivedPlus
  let adj' := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (pullback.snd f g'')).derivedPlus
  let θ := TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom
  have hβ : (mateEquiv adj adj' θ) =
      derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq := by
    apply derivedBaseChangeMapPlus_ext AddCommGrpCat.{u + 1} sq
    intro K
    exact Adjunction.derivedPlus_mateEquiv_app_fac
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.snd f g'))
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.snd f g''))
      (TwoSquare.mk _ _ _ _ (squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom)
      θ (pullbackSquareComparison_hom_app_factorsh AddCommGrpCat.{u + 1} sq) K
  let : NatTrans.CommShift (mateEquiv adj adj' θ) ℤ := by
    rw [hβ]
    infer_instance
  let δ := (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} b a a' ha).hom.app
        ((abelianComparisonFree B).obj V)) ≫
    (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
        (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V))
  have hm := shifted_adjunct_mate_transport adj adj'
    D+((b)^*[AddCommGrpCat.{u + 1}]) D+((t)^*[AddCommGrpCat.{u + 1}]) θ
    (n : ℤ) δ ((cartesianChartAdjunctIso f g a g' w F n V).hom z)
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} t (pullback.fst f g')
      (pullback.fst f g'') (cartesianImageProjection_fst f g' g'' b wb).symm).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  rw [hβ] at hm
  dsimp only [θ, TwoSquare.mk, δ] at hm
  have ht := actualTransport_eq AddCommGrpCat.{u + 1}
    (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom a a' ha
    (pullback.fst f g') (pullback.fst f g'')
    (cartesianImageProjection_fst f g' g'' b wb).symm
    ((abelianComparisonFree B).obj V) F n
    ((cartesianChartAdjunctIso f g a g' w F n V).hom z)
  rw [← ht] at hm
  rw [← chartAdjunct_pullback f g a g' w b a' ha g'' w' wb l hl₁ hl₂ F n V z] at hm
  dsimp only [adj, adj'] at hm
  rw [cartesianChartAdjunct_spec, cartesianChartAdjunct_spec] at hm
  simpa only [cartesianDerivedImageMap, cartesianDerivedImage, t, sq, Category.assoc] using hm

end AlgebraicGeometry.Etale
