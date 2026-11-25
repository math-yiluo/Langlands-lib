/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginOpenRestrictionTransport
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Etale-origin proper/open interchange

Source: retained repaired proof of blueprint main-20261015,
`proposition-composition-open-restriction-compactifications-f--5`, Step 7; Stacks Tags 099R and 0F7B
(blueprint: lem-exc-etale-origin-proper-open-interchange).

The five arrows use the published fixed-scalar comparisons, transported through the
canonical intrinsic realization. No ambient exceptional adjunction is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- The specified etale interchange, selected together with its full representative and
open-adjunction normalization. Those conditions determine the map on all objects.
Source: Stacks Tag 0F7B, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginOpenEtaleInterchange {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)] :
    (Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor ⋙
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory ≅
    (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor :=
  Etale.properOpenCoefficientInterchange (ULift.{u + 1, u} A)
    (IsPullback.of_hasPullback p i)

/-- The five-arrow site-transport composite. The two intervening Plus compatibility
isomorphisms merely identify termwise open extension before and after inclusion into D.
Source: retained blueprint Step 7, five-arrow display; Stacks Tags 099R and 0F7B
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginProperOpenIso {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicDerivedOpen A i).obj
        ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) ≅
      (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) :=
  let ke := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)
  let pe := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)
  (sfIntrinsicDerivedOpen A i).mapIso
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).symm ≪≫
    (etaleOriginOpenExtensionComparison A i).symm.app (re.rightDerivedFunctor.obj K.obj) ≪≫
    (etaleOriginOpenComparison A T).mapIso
      ((etaleOriginOpenEtaleInterchange A p i).app K.obj) ≪≫
    (etaleOriginOpenComparison A T).mapIso
      (pe.rightDerivedFunctor.mapIso (ke.mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    etaleOriginOpenDirectImageComparison A p (ke.mapDerivedCategoryPlus.obj K) ≪≫
    (proEtaleConstantDerivedDirectImage p A).mapIso
      ((etaleOriginOpenComparison A V).mapIso (ke.mapDerivedCategoryPlusCompatibility.app K) ≪≫
        (etaleOriginOpenExtensionComparison A (pullback.fst p i)).app K.obj)

attribute [local irreducible] etaleOriginOpenComparison etaleOriginOpenCoordinates
  etaleOriginOpenExtensionComparison etaleOriginOpenDirectImageComparison
  etaleOriginProperOpenIso
  sfIntrinsicDerivedEquivalence sfIntrinsicModuleEquivalence sfIntrinsicExtensionByZero
  sfIntrinsicPullback exceptionalOpenAdjunction
  Etale.lowerStar Etale.upperStar Etale.openImmersionLowerShriek

end AlgebraicGeometry.Scheme
