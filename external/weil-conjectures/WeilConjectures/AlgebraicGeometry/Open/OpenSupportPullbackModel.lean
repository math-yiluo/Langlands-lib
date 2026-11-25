/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.Compactification.BaseChange

/-! # The proper/open comparison before changing compactifications
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The comparison for the literal pullback of one compactification. This is the
proper/open and open-composition part of `openSupportCompactificationIso`, with no
initial graph comparison. -/
def openSupportPullbackIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (cf : Compactification f) :
    Rf_!(cf.ofIsPullback sq)[ModuleCat.{u + 1} Λ] ⋙
        D((j)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((a)_!open[ModuleCat.{u + 1} Λ]) ⋙ Rf_!(cf)[ModuleCat.{u + 1} Λ] := by
  let A := ModuleCat.{u + 1} Λ
  let cq := cf.ofIsPullback sq
  let k := pullback.fst cf.g j
  let ex := openImmersionLowerShriekLowerStarExchangeIso Λ
    (IsPullback.of_hasPullback cf.g j).flip
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ex ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((mapDerivedCategoryOpenImmersionLowerShriekComp A cq.i k).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr A
          (cf.ofIsPullback_i_fst sq) ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp A a cf.i) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Etale
