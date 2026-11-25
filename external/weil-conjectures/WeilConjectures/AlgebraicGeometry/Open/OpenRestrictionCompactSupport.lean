/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-! # Compact support and restriction to an arbitrary open

The graph comparisons specify the comparison even when the open is not quasi-compact.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The specified graph comparison of two compactifications, without a qc assumption. -/
def openRestrictionGraphIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c d : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ≅ Rf_!(d)[ModuleCat.{u + 1} Λ] :=
  sfGraphCompactificationComparison Λ c d.g d.i (𝟙 X)
      (by simpa using d.comm.symm) ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarIdIso Λ X) _ ≪≫
    Functor.leftUnitor _

/-- Open extension commutes with compact support on a cartesian square. The comparison
is constructed from graph comparison, proper/open interchange, and open composition. -/
def openRestrictionCompactSupportIso {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} [HasCompactification f] {j : U ⟶ Y} [IsOpenImmersion j]
    {a : V ⟶ X} [IsOpenImmersion a] {p : V ⟶ U}
    (sq : IsPullback a p f j) [HasCompactification p] :
    R(p)_![ModuleCat.{u + 1} Λ] ⋙ D((j)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((a)_!open[ModuleCat.{u + 1} Λ]) ⋙ R(f)_![ModuleCat.{u + 1} Λ] := by
  let A := ModuleCat.{u + 1} Λ
  let cf := HasCompactification.compactification f
  let cp := cf.ofIsPullback sq
  let k := pullback.fst cf.g j
  let e := openRestrictionGraphIso Λ (HasCompactification.compactification p) cp
  let ex := openImmersionLowerShriekLowerStarExchangeIso Λ
    (IsPullback.of_hasPullback cf.g j).flip
  exact Functor.isoWhiskerRight e _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ex ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((mapDerivedCategoryOpenImmersionLowerShriekComp A cp.i k).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr A
          (cf.ofIsPullback_i_fst sq) ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp A a cf.i) _ ≪≫
    Functor.associator _ _ _

/-- The right adjoint comparison obtained from the explicitly constructed support comparison. -/
def openRestrictionExceptionalIso {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} [HasCompactification f] {j : U ⟶ Y} [IsOpenImmersion j]
    {a : V ⟶ X} [IsOpenImmersion a] {p : V ⟶ U}
    (sq : IsPullback a p f j) [HasCompactification p] :
    R(f)^![Λ] ⋙ L((a)^*[ModuleCat.{u + 1} Λ]) ≅
      L((j)^*[ModuleCat.{u + 1} Λ]) ⋙ R(p)^![Λ] := by
  exact conjugateIsoEquiv
    ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ a).comp
      (rightDerivedUpperShriekAdjunction _ f))
    ((rightDerivedUpperShriekAdjunction _ p).comp
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j))
    (openRestrictionCompactSupportIso Λ sq)

end AlgebraicGeometry.Etale
