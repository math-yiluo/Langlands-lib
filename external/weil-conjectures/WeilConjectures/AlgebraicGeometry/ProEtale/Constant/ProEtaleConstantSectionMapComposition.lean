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
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Composition of pro-etale constant-section maps

## References

* Stacks Project, Tag 09A5, final paragraphs
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Constant-section maps compose through the canonical direct-image comparison.
Here the coefficient object is the regular `A`-module, and `lowerStarComp` is restriction
along the canonical fibre-product associativity isomorphism (with the variable factor
first in the chosen pullbacks). -/
theorem proEtaleConstantDirectImageMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleConstantDirectImageMap (f ≫ g) (ModuleCat.{u + 1} A) (ModuleCat.of A A) =
      proEtaleConstantDirectImageMap g (ModuleCat.{u + 1} A) (ModuleCat.of A A) ≫
        (proEtaleSheafDirectImage g (ModuleCat.{u + 1} A)).map
          (proEtaleConstantDirectImageMap f (ModuleCat.{u + 1} A) (ModuleCat.of A A)) ≫
        (AlgebraicGeometry.ProEtale.lowerStarComp (ModuleCat.{u + 1} A) f g).hom.app
          ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)) := by
  apply ((sheafificationAdjunction (ProEt.topology Z) (ModuleCat.{u + 1} A)).homEquiv
    ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of A A)) _).injective
  rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right]
  rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  have hf := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of A A))
        ((proEtaleSheafDirectImage f (ModuleCat.{u + 1} A)).obj
          ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A))))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))))
  have hfU := congrArg (fun t ↦ t.app ((proEtaleBaseChange g).op.obj U)) hf
  change (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
      ((proEtaleBaseChange g).op.obj U) ≫
    (proEtaleConstantDirectImageMap f (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)).hom.app ((proEtaleBaseChange g).op.obj U) =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
        ((proEtaleBaseChange f).op.obj ((proEtaleBaseChange g).op.obj U)) at hfU
  change (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
      ((proEtaleBaseChange (f ≫ g)).op.obj U) =
    ((toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
        ((proEtaleBaseChange g).op.obj U) ≫
      (proEtaleConstantDirectImageMap f (ModuleCat.{u + 1} A)
        (ModuleCat.of A A)).hom.app ((proEtaleBaseChange g).op.obj U)) ≫
      ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A)).obj.map
        ((MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
  rw [hfU]
  have h := (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).naturality
    ((MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
  change 𝟙 (ModuleCat.of A A) ≫ _ = _ at h
  rw [Category.id_comp] at h
  exact h

end AlgebraicGeometry.Scheme
