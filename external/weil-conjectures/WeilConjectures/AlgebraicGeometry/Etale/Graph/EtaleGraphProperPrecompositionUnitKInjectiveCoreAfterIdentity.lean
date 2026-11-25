/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCompositorGraphTranspose
import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperSheafUnitGraphTranspose
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraFrobenius

/-! # Component of proper-first graph normalization

This is the K-injective component calculation in the proof of
`graph_proper_precomposition_unit` (blueprint: lem-pur-graph-proper-precomposition-unit).
It isolates the objectwise geometric calculation; natural-transformation extensionality is
handled in the parent module.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor canonicalEtaleCompactSupportComparison
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

private lemma comp_homotopy_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app J = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

/-- The representative graph equation after postcomposition by the codomain identity.
Source: Stacks Project, Tags 0F7B, 0F7I and 0F7J; representative-complex normalization.

Proof in words: transpose both maps under the exact étale extension/pullback adjunction
and compose with proper base change for c.g. The compositor transpose is the clopen graph
transfer. The normalized sheaf map transpose is the same transfer preceded by the q-unit.
Naturality of adjunction transposition identifies the two expressions. Proper base change
is invertible, so cancellation and injectivity of the adjunction equivalence recover the
original equality. Finally cancel the exact functor's homotopy factor isomorphism.
(blueprint: lem-pur-graph-proper-precomposition-unit-component-core-after-identity).
-/
theorem graph_proper_precomposition_unit_component_on_complex_after_identity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    {f : W ⟶ Y} (hf : f = q ≫ v) [HasCompactification f]
    (c : Compactification f)
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      τ.app F ≫ (compactificationSheafToDirectImage A c).app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v f hf).hom.app F)
    (K : HomologicalComplex
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    𝟙 _ ≫
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
        (lowerStar (ModuleCat.{u + 1} A) q)
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
            (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
            (graphChosenEtaleComparison A v).symm ≪≫
          unboundedEtaleLowerShriekCompIso A q v ≪≫
          unboundedEtaleLowerShriekCongr A hf.symm ≪≫
          (rightDerivedLowerShriekIso A c).symm).hom).app
      ((HomotopyCategory.quotient
        (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).obj K) =
      𝟙 _ ≫
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ))
          DerivedCategory.Qh ≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
          (lowerStar (ModuleCat.{u + 1} A) c.g)).app
        ((HomotopyCategory.quotient
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).obj K) := by
  let B := ModuleCat.{u + 1} A
  let J := (HomotopyCategory.quotient (Sheaf W.smallEtaleTopology B) (.up ℤ)).obj K
  let G := etaleLowerShriek B v inferInstance
  let e : rightDerivedLowerStar B q ⋙ G.mapDerivedCategory ≅
      (openImmersionLowerShriek B c.i).mapDerivedCategory ⋙ rightDerivedLowerStar B c.g :=
    Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
      (graphChosenEtaleComparison A v).symm ≪≫
    unboundedEtaleLowerShriekCompIso A q v ≪≫
    unboundedEtaleLowerShriekCongr A hf.symm ≪≫
    (rightDerivedLowerShriekIso A c).symm
  let a := derivedEtaleLowerShriekUpperStarAdjunction B v inferInstance
  let β := (exactDerivedBaseChangeMap B
    (IsPullback.of_hasPullback c.g v).toCommSq).app
      ((openImmersionLowerShriek B c.i).mapDerivedCategory.obj (DerivedCategory.Qh.obj J))
  have : IsIso (exactDerivedBaseChangeMap B
      (IsPullback.of_hasPullback c.g v).toCommSq) :=
    ProperGraphTransfer.baseChange_isIso v c A
  have hleft :
      a.homEquiv _ _
          (G.mapDerivedCategory.map ((lowerStar B q).rightDerivedFunctorUnit.app J) ≫
            e.hom.app (DerivedCategory.Qh.obj J)) ≫ β =
        (lowerStar B q).rightDerivedFunctorUnit.app J ≫
          ProperGraphTransfer.transfer q v hf c A (DerivedCategory.Qh.obj J) := by
    rw [a.homEquiv_naturality_left, Category.assoc]
    exact congrArg ((lowerStar B q).rightDerivedFunctorUnit.app J ≫ ·)
      (properCompositor_graph_transpose A q v hf c (DerivedCategory.Qh.obj J))
  have hright := properSheafUnit_graph_transpose A q v hf c τ hτ J
  have hc :
      G.mapDerivedCategory.map ((lowerStar B q).rightDerivedFunctorUnit.app J) ≫
          e.hom.app (DerivedCategory.Qh.obj J) =
        G.mapDerivedCategoryFactorsh.hom.app
            ((lowerStar B q).mapHomotopyCategory (.up ℤ) |>.obj J) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
            (openImmersionLowerShriek B c.i) (lowerStar B c.g)).app J := by
    apply (a.homEquiv _ _).injective
    apply (cancel_mono β).1
    exact hleft.trans hright.symm
  simp only [Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app,
    comp_homotopy_inv, DerivedCategory.Qh.map_id, Category.id_comp]
  rw [Category.assoc]
  change G.mapDerivedCategoryFactorsh.inv.app
      ((lowerStar B q).mapHomotopyCategory (.up ℤ) |>.obj J) ≫
      G.mapDerivedCategory.map ((lowerStar B q).rightDerivedFunctorUnit.app J) ≫
      e.hom.app (DerivedCategory.Qh.obj J) = _
  exact (congrArg
    (G.mapDerivedCategoryFactorsh.inv.app
      ((lowerStar B q).mapHomotopyCategory (.up ℤ) |>.obj J) ≫ ·) hc).trans
        (Iso.inv_hom_id_app_assoc G.mapDerivedCategoryFactorsh _ _)

end AlgebraicGeometry.Etale
