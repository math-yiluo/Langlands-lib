/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence

/-!
# Composition of canonical constant-ring maps on pro-etale sites

The inverse-image comparison is the adjunction mate of the canonical
fibre-product associativity comparison on direct images. The coefficient maps are
exactly the adjuncts of the constant-section maps.

## References

* Stacks Project, Tag 09A5 (Functoriality of the pro-etale site), together with Tags 0H7J and 00WH
  (constant sheaves and sheafification)
* Stacks Project, Tag 09A5, with Tags 0H7J and 00WH
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem homEquiv_mate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (d : R' ≅ R) {X : C} {Y : D} (t : L'.obj X ⟶ Y) :
    a.homEquiv X Y
        (((conjugateIsoEquiv a b).symm d.symm).inv.app X ≫ t) =
      b.homEquiv X Y t ≫ d.hom.app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc]
  change (a.unit.app X ≫
      R.map (((conjugateEquiv b a).symm d.hom).app X)) ≫ R.map t = _
  rw [← unit_conjugateEquiv_symm b a d.hom X, Category.assoc, ← d.hom.naturality]
  simp only [Category.assoc]

private theorem rho_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))))
  exact congrArg (fun t ↦ t.app W) h

private noncomputable def sheafComp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y) :
    proEtaleSheafDirectImage b CommRingCat.{u + 1} ⋙
      proEtaleSheafDirectImage a CommRingCat.{u + 1} ≅
        proEtaleSheafDirectImage (b ≫ a) CommRingCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).symm)
    CommRingCat.{u + 1} (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)

private theorem rho_comp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleCoefficientDirectImageMap a A ≫
      (proEtaleSheafDirectImage a CommRingCat.{u + 1}).map
        (proEtaleCoefficientDirectImageMap b A) ≫
          (sheafComp a b).hom.app (proEtaleConstantRing X A) =
            proEtaleCoefficientDirectImageMap (b ≫ a) A := by
  apply (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext W
  change _ ≫ _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc, ← Category.assoc, rho_unit]
  change ((toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange a).op.obj W) ≫
      (proEtaleCoefficientDirectImageMap b A).hom.app
        ((proEtaleBaseChange a).op.obj W)) ≫
      (proEtaleConstantRing X A).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
          W.unop).op =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
        (proEtaleCoefficientDirectImageMap (b ≫ a) A).hom.app W
  rw [rho_unit, rho_unit]
  have hn := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).naturality
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
        W.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  exact hn.symm.trans (Category.id_comp _)

/-- The canonical constant-ring coefficient maps respect composition of scheme morphisms. -/
theorem proEtaleCoefficientInverseImageMap_comp
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleCoefficientInverseImageMap (h ≫ k) A =
      (ProEtale.supportSiteProEtaleComparisonComp CommRingCat.{u + 1} h k).hom.app
          (proEtaleConstantRing V A) ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (proEtaleCoefficientInverseImageMap k A) ≫
        proEtaleCoefficientInverseImageMap h A := by
  let a := proEtaleSheafAdjunction (h ≫ k) CommRingCat.{u + 1}
  let b := (proEtaleSheafAdjunction k CommRingCat.{u + 1}).comp
    (proEtaleSheafAdjunction h CommRingCat.{u + 1})
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _ ((a.homEquiv _ _).symm
      (proEtaleCoefficientDirectImageMap (h ≫ k) A)) = _
  rw [Equiv.apply_symm_apply]
  change _ = a.homEquiv _ _
    (((conjugateIsoEquiv a b).symm (sheafComp k h).symm).inv.app _ ≫ _)
  rw [homEquiv_mate]
  change _ = ((proEtaleSheafAdjunction k CommRingCat.{u + 1}).comp
    (proEtaleSheafAdjunction h CommRingCat.{u + 1})).homEquiv _ _ _ ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (proEtaleSheafAdjunction k CommRingCat.{u + 1}).homEquiv _ _
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _
      ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (proEtaleCoefficientInverseImageMap k A) ≫
        proEtaleCoefficientInverseImageMap h A)) ≫ _
  rw [Adjunction.homEquiv_naturality_left]
  have hh := ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _)
    |>.apply_symm_apply (proEtaleCoefficientDirectImageMap h A)
  have hk := ((proEtaleSheafAdjunction k CommRingCat.{u + 1}).homEquiv _ _)
    |>.apply_symm_apply (proEtaleCoefficientDirectImageMap k A)
  change (proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _
    (proEtaleCoefficientInverseImageMap h A) = _ at hh
  change (proEtaleSheafAdjunction k CommRingCat.{u + 1}).homEquiv _ _
    (proEtaleCoefficientInverseImageMap k A) = _ at hk
  rw [hh, Adjunction.homEquiv_naturality_right, hk]
  exact (rho_comp k h A).symm

end AlgebraicGeometry.Scheme
