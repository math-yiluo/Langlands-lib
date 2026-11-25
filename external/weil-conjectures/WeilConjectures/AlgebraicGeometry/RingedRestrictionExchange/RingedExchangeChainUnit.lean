/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare

/-! Shared ordinary operations and the cochain-unit normalization of ringed exchange.

## References

* Stacks Project, Derived Categories, Tags 070K and 09T5
* Stacks 09T5 and 09A5
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingModulePullback proEtaleRingModuleDirectImage proEtaleRingModuleAdjunction
  proEtaleCanonicalDerivedPullbackComparison StrictTowerRingedSquare.exchangeModuleSquare

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- The source vertical inverse image. -/
abbrev verticalPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback f r.RY r.RX r.cf

/-- The source vertical direct image. -/
abbrev verticalPush (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleDirectImage f r.RY r.RX r.cf

/-- The base inverse image. -/
abbrev basePull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback g r.RY r.RY' r.cg

/-- The inverse image on the upper side of the square. -/
abbrev upperPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback g' r.RX r.RX' r.cg'

/-- The target vertical inverse image. -/
abbrev targetPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback f' r.RY' r.RX' r.cf'

/-- The target vertical direct image. -/
abbrev targetPush (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleDirectImage f' r.RY' r.RX' r.cf'

/-- The ordinary counit mate, prior to deriving. -/
def ordinary (r : StrictTowerRingedSquare sq) :
    verticalPush r ⋙ basePull r ⟶ upperPull r ⋙ targetPush r :=
  (mateEquiv (proEtaleRingModuleAdjunction f r.RY r.RX r.cf)
    (proEtaleRingModuleAdjunction f' r.RY' r.RX' r.cf')
    (TwoSquare.mk _ _ _ _ r.exchangeModuleSquare.hom))

/-- The derived counit mate for the ordinary-derived adjunctions. -/
abbrev exchange (r : StrictTowerRingedSquare sq) :
    (verticalPush r).rightDerivedFunctor ⋙ (basePull r).mapDerivedCategory ⟶
      (upperPull r).mapDerivedCategory ⋙ (targetPush r).rightDerivedFunctor :=
  proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent

section Comparisons
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

/-- The comparison Q(FK) → RF(QK) for any additive direct image. -/
def chainComparison [Abelian.HasKInjectiveResolutions C] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app K)

private theorem cochainUnit_eq_chainComparison [Abelian.HasKInjectiveResolutions C]
    (K : CochainComplex C ℤ) :
    UnboundedExactTower.cochainUnit F K = chainComparison F K := by
  simp only [UnboundedExactTower.cochainUnit, chainComparison,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
end Comparisons

section GenericMate
universe vA vB vA' vB' uA uB uA' uB'
variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  {F : B ⥤ A} {F' : B' ⥤ A'} {G : A ⥤ B} {G' : A' ⥤ B'}
  (P : B ⥤ B') (H : A ⥤ A')
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [P.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']

-- Fix the nested-complex hom-set before substituting the ordinary mate.
private theorem chain_mate (a : F ⊣ G) (a' : F' ⊣ G')
    (θ : P ⋙ F' ≅ F ⋙ H)
    (δ : P.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hδ : δ = Functor.mapDerivedCategorySquareIso θ)
    (m : G ⋙ P ⟶ H ⋙ G')
    (hm : m = (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)))
    (e : G.rightDerivedFunctor ⋙ P.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (he : e = (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      a'.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ δ.hom)))
    (K : CochainComplex A ℤ)
    (β : DerivedCategory.Q.obj ((P.mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj K)) ⟶
      DerivedCategory.Q.obj ((G'.mapHomologicalComplex (.up ℤ)).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj K)))
    (hβ : β = DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex m (.up ℤ)).app K)) :
    P.mapDerivedCategory.map (chainComparison G K) ≫
        e.app (DerivedCategory.Q.obj K) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
      P.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        β ≫
        chainComparison G' ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
  subst β
  subst m
  subst e
  subst δ
  have h := UnboundedExactTower.localized_mate_cochain_normalization a a' θ K
  apply (cancel_epi (P.mapDerivedCategoryFactors.inv.app
    ((G.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simpa only [cochainUnit_eq_chainComparison, UnboundedExactTower.localizedSquare,
    Functor.mapDerivedCategorySquareIso, Category.assoc] using h
end GenericMate

-- Preserve the public category expressions and their native instances while the functors
-- are still variables, so specialization does not unfold concrete sheaf tensor objects.
section SchemeMate
variable (r : StrictTowerRingedSquare sq)
  {F : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules X r.RX}
  {F' : proEtaleRingModules Y' r.RY' ⥤ proEtaleRingModules X' r.RX'}
  {G : proEtaleRingModules X r.RX ⥤ proEtaleRingModules Y r.RY}
  {G' : proEtaleRingModules X' r.RX' ⥤ proEtaleRingModules Y' r.RY'}
  (P : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
  (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [P.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem scheme_chain_mate (a : F ⊣ G) (a' : F' ⊣ G')
    (θ : P ⋙ F' ≅ F ⋙ H)
    (δ : P.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hδ : δ = Functor.mapDerivedCategorySquareIso θ)
    (m : G ⋙ P ⟶ H ⋙ G')
    (hm : m = (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)))
    (e : G.rightDerivedFunctor ⋙ P.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (he : e = (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      a'.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ δ.hom)))
    (K : CochainComplex (proEtaleRingModules X r.RX) ℤ) :
    P.mapDerivedCategory.map (chainComparison G K) ≫
        e.app (DerivedCategory.Q.obj K) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
      P.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex m (.up ℤ)).app K) ≫
        chainComparison G' ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
  exact chain_mate P H a a' θ δ hδ m hm e he K _ rfl
end SchemeMate

private theorem ordinary_mate (r : StrictTowerRingedSquare sq) :
    ordinary r = (mateEquiv (proEtaleRingModuleAdjunction f r.RY r.RX r.cf)
      (proEtaleRingModuleAdjunction f' r.RY' r.RX' r.cf')
      (TwoSquare.mk _ _ _ _ r.exchangeModuleSquare.hom)) := rfl

private theorem exchange_mate (r : StrictTowerRingedSquare sq) :
    exchange r = (mateEquiv
      (proEtaleRingModuleAdjunction f r.RY r.RX r.cf).mapDerivedCategoryRightDerivedAdjunction
      (proEtaleRingModuleAdjunction f' r.RY' r.RX' r.cf').mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (proEtaleAmbientRingedPullbackComparison sq
        r.RX r.RY r.RX' r.RY' r.cf r.cg r.cg' r.cf' r.coherent).hom)) := rfl

/-- The chosen exchange commutes with the canonical right-derived cochain units. -/
theorem exchange_chainUnit (r : StrictTowerRingedSquare sq)
    (K : CochainComplex (proEtaleRingModules X r.RX) ℤ) :
    (basePull r).mapDerivedCategory.map (chainComparison (verticalPush r) K) ≫
        (exchange r).app (DerivedCategory.Q.obj K) ≫
        (targetPush r).rightDerivedFunctor.map
          ((upperPull r).mapDerivedCategoryFactors.hom.app K) =
      (basePull r).mapDerivedCategoryFactors.hom.app
          (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinary r) (.up ℤ)).app K) ≫
        chainComparison (targetPush r)
          (((upperPull r).mapHomologicalComplex (.up ℤ)).obj K) := by
  have h := scheme_chain_mate r
    (F := verticalPull r) (F' := targetPull r)
    (G := verticalPush r) (G' := targetPush r) (basePull r) (upperPull r)
    (proEtaleRingModuleAdjunction f r.RY r.RX r.cf)
    (proEtaleRingModuleAdjunction f' r.RY' r.RX' r.cf') r.exchangeModuleSquare
    (proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
      r.cf r.cg r.cg' r.cf' r.coherent) r.ambientSquare_localization
    (ordinary r) (ordinary_mate r) (exchange r) (exchange_mate r) K
  exact h

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
