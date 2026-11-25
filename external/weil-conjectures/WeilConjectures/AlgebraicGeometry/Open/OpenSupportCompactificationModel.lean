/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionCompactSupport

/-! # Open-support comparisons with supplied compactifications
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The open-support comparison with both compactifications supplied explicitly.
It uses the same graph, proper/open, and open-composition factors as the chosen
comparison. -/
def openSupportCompactificationIso {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} {j : U ⟶ Y} [IsOpenImmersion j]
    {a : V ⟶ X} [IsOpenImmersion a] {p : V ⟶ U}
    (sq : IsPullback a p f j) (cf : Compactification f) (cp : Compactification p) :
    Rf_!(cp)[ModuleCat.{u + 1} Λ] ⋙ D((j)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((a)_!open[ModuleCat.{u + 1} Λ]) ⋙ Rf_!(cf)[ModuleCat.{u + 1} Λ] := by
  let A := ModuleCat.{u + 1} Λ
  let cq := cf.ofIsPullback sq
  let k := pullback.fst cf.g j
  let e := openRestrictionGraphIso Λ cp cq
  let ex := openImmersionLowerShriekLowerStarExchangeIso Λ
    (IsPullback.of_hasPullback cf.g j).flip
  exact Functor.isoWhiskerRight e _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ex ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((mapDerivedCategoryOpenImmersionLowerShriekComp A cq.i k).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr A
          (cf.ofIsPullback_i_fst sq) ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp A a cf.i) _ ≪≫
    Functor.associator _ _ _

/-- Base change before changing the output compactification. Proper base change
makes the raw exchange invertible for finite coefficients. -/
def compactificationSupportBaseChangeIso
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (cf : Compactification f) :
    Rf_!(cf)[ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙
        Rf_!(cf.ofIsPullback sq)[ModuleCat.{u + 1} Λ] := by
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite (IsPullback.of_hasPullback cf.g g)
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} Λ) sq cf
  exact asIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq cf)

end AlgebraicGeometry.Etale
