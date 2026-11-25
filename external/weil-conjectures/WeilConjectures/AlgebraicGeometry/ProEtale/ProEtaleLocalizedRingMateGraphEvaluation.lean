/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Localized ring-sheaf mates evaluated on graphs

The helpers only expand the maps in the statement. In particular the mate uses the
specified Kan-extension/sheafification adjunction, and both forgetful and integer-unit
comparisons use the coprojection-normalized restriction comparisons.

## References

* Stacks Project, Sites and Sheaves, Tags 03CE, 00Y0, 00VE and 00WX
* Modules on Sites, Tag 03EL
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem inverseImageUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type*) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D]
    (R : Sheaf (ProEt.topology Y) D) :
    ((proEtaleSheafAdjunction f D).unit.app R).hom =
      (proEtaleBaseChange f).op.lanUnit.app R.obj ≫
        (proEtaleBaseChange f).op.whiskerLeft
          (toSheafify (ProEt.topology X) ((proEtaleBaseChange f).op.lan.obj R.obj)) := by
  change (sheafToPresheaf _ _).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).unit.app R) = _
  erw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedUnit {B : Scheme.{u}} (V : B.ProEt)
    (D : Type*) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology V.left) D]
    (c : ProEtaleObjectRestrictionComparison V D)
    (R : Sheaf (ProEt.topology B) D) (T : B.ProEt) :
    ((proEtaleSheafAdjunction (X := V.left) (Y := B) V.hom D).unit.app R).hom.app (op T) ≫
      (c.sheafIso.hom.app R).hom.app (op ((proEtaleBaseChange V.hom).obj T)) =
    R.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
      V.hom V.prop trivial).counit.app T).op := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop trivial
  let W := (proEtaleBaseChange V.hom).obj T
  let L := (proEtaleBaseChange V.hom).op.lan.obj R.obj
  apply (cancel_mono ((c.sheafIso.inv.app R).hom.app (op W))).mp
  simp only [Category.assoc]
  have hi := congrArg (fun z ↦ z.hom.app (op W)) (c.sheafIso.hom_inv_id_app R)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hi
  erw [hi, Category.comp_id]
  erw [c.sheafIso_inv]
  dsimp only [NatTrans.comp_app]
  erw [c.coprojection, inverseImageUnit]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  have hn := ((proEtaleBaseChange V.hom).op.lanUnit.app R.obj).naturality
    (a.counit.app T).op
  erw [← Category.assoc, ← Category.assoc, hn]
  change ((proEtaleBaseChange V.hom).op.lanUnit.app R.obj).app (op T) ≫
      (toSheafify (ProEt.topology V.left) L).app (op W) =
    ((((proEtaleBaseChange V.hom).op.lanUnit.app R.obj).app (op T) ≫
      L.map ((proEtaleBaseChange V.hom).op.map (a.counit.app T).op)) ≫
        L.map (proEtaleObjectInverseImageIndexPoint V W).hom.op) ≫
          (toSheafify (ProEt.topology V.left) L).app (op W)
  simp only [Category.assoc]
  erw [← L.map_comp_assoc]
  have ht := congrArg Quiver.Hom.op (a.right_triangle_components T)
  have ht' : (proEtaleBaseChange V.hom).op.map (a.counit.app T).op ≫
      (proEtaleObjectInverseImageIndexPoint V W).hom.op = 𝟙 (op W) := ht
  erw [ht', L.map_id, Category.id_comp]

end AlgebraicGeometry.Scheme
