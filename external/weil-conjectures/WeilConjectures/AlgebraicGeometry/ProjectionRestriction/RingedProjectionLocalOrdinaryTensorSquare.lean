/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalPullbackNormalization
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Ordinary tensor coherence for the localized adjunction mate

## References

* Stacks Project, Modules on Sites, Tag 04J0
* Cohomology on Sites, Tag 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

private theorem square_unit_sections
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    {g : Global f R_Y R_X c} {V : Y.ProEt}
    (l : Local f R_Y R_X c g V) (M : Mod R_Y) (W : (Over V)ᵒᵖ)
    (x : M.val.obj (op W.unop.left)) :
    ((l.operation.pushforward.map ((localOrdinaryPullbackSquare l).app M)).val.app W)
        ((l.operation.moduleAdjunction.unit.app (M.over V)).val.app W x) =
      (g.operation.moduleAdjunction.unit.app M).val.app (op W.unop.left) x := by
  have h := unit_mateEquiv_symm g.operation.moduleAdjunction
    l.operation.moduleAdjunction (TwoSquare.mk _ _ _ _ l.ordinaryDirectImage.hom) M
  have hh := congrArg (fun k ↦ k.val.app W x) h
  change ((l.ordinaryDirectImage.hom.app (g.operation.pullback.obj M)).val.app W)
      ((g.operation.moduleAdjunction.unit.app M).val.app (op W.unop.left) x) =
    ((l.operation.pushforward.map ((localOrdinaryPullbackSquare l).app M)).val.app W)
      ((l.operation.moduleAdjunction.unit.app (M.over V)).val.app W x) at hh
  exact hh.symm.trans (l.ordinaryDirectImage_sections _ W _)

attribute [local irreducible] SheafOfModules.monoidalCategory
  localOrdinaryPullbackSquare Operation.moduleAdjunction

-- The four section formulas involve the global and slice module adjunction presentations.
/-- The ordinary inverse mate commutes with the two pullback and two restriction
comparisons on module sheaves, without derived categories or resolving complexes. -/
theorem localOrdinaryTensorSquare
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt)
    (l : Local f R_Y R_X c g V) (M N : Mod R_Y) :
    (localOrdinaryPullbackSquare l).app (((tensor R_Y).obj M).obj N) ≫
        (SheafOfModules.overFunctor.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
          ((proEtaleBaseChange f).obj V)).map (g.ordinaryTensor.iso M N).hom ≫
        (l.restrictionX.ordinaryTensor (g.operation.pullback.obj M)
          (g.operation.pullback.obj N)).hom =
      l.operation.pullback.map (l.restrictionY.ordinaryTensor M N).hom ≫
        (l.ordinaryTensor.iso (M.over V) (N.over V)).hom ≫
        (Functor.uncurry.obj (tensor (R_X.over ((proEtaleBaseChange f).obj V)))).map
          (Prod.mkHom ((localOrdinaryPullbackSquare l).app M)
            ((localOrdinaryPullbackSquare l).app N)) := by
  let rY := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V
  let rX := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
    ((proEtaleBaseChange f).obj V)
  let t := localOrdinaryPullbackSquare l
  apply (l.operation.moduleAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (cancel_epi (l.restrictionY.ordinaryTensor M N).inv).1
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (R_Y.over V)
    (M.over V) (N.over V)
  intro W x y
  have hback : ((l.restrictionY.ordinaryTensor M N).inv.val.app W)
      (pure (R_Y.over V) (M.over V) (N.over V) W x y) =
    pure R_Y M N (op W.unop.left) x y := by
    have h := congrArg
      (fun z ↦ ((l.restrictionY.ordinaryTensor M N).inv.val.app W) z)
      (l.restrictionY.pure_sections M N W x y)
    have hi := congrArg
      (fun z ↦ z.val.app W (pure R_Y M N (op W.unop.left) x y))
      (l.restrictionY.ordinaryTensor M N).hom_inv_id
    change ((l.restrictionY.ordinaryTensor M N).inv.val.app W)
      (((l.restrictionY.ordinaryTensor M N).hom.val.app W)
        (pure R_Y M N (op W.unop.left) x y)) = _ at hi
    exact h.symm.trans hi
  have hn := l.operation.moduleAdjunction.unit.naturality
    (l.restrictionY.ordinaryTensor M N).hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  let T := (Over.post (X := V) (proEtaleBaseChange f)).op.obj W
  have hu := congrArg
    (fun k ↦ k.val.app W (pure R_Y M N (op W.unop.left) x y)) hn
  change ((l.operation.moduleAdjunction.unit.app
      (((tensor (R_Y.over V)).obj (M.over V)).obj (N.over V))).val.app W)
      (((l.restrictionY.ordinaryTensor M N).hom.val.app W)
        (pure R_Y M N (op W.unop.left) x y)) =
    ((l.operation.pushforward.map
      (l.operation.pullback.map (l.restrictionY.ordinaryTensor M N).hom)).val.app W)
      ((l.operation.moduleAdjunction.unit.app _).val.app W
        (pure R_Y M N (op W.unop.left) x y)) at hu
  rw [l.restrictionY.pure_sections] at hu
  have hM := square_unit_sections l M W x
  have hN := square_unit_sections l N W y
  have hTensor := square_unit_sections l (((tensor R_Y).obj M).obj N) W
    (pure R_Y M N (op W.unop.left) x y)
  have hmap := SheafOfModules.CochainScalarConstruction.pure_map
    (R_X.over ((proEtaleBaseChange f).obj V)) (t.app M) (t.app N) T
    ((l.operation.moduleAdjunction.unit.app (M.over V)).val.app W x)
    ((l.operation.moduleAdjunction.unit.app (N.over V)).val.app W y)
  simp only [CategoryTheory.MonoidalCategory.tensorHom_def] at hmap
  change ((Functor.uncurry.obj (tensor (R_X.over ((proEtaleBaseChange f).obj V)))).map
      (Prod.mkHom (t.app M) (t.app N))).val.app T
      (pure (R_X.over ((proEtaleBaseChange f).obj V)) _ _ T
        ((l.operation.moduleAdjunction.unit.app (M.over V)).val.app W x)
        ((l.operation.moduleAdjunction.unit.app (N.over V)).val.app W y)) = _ at hmap
  change _ = pure (R_X.over ((proEtaleBaseChange f).obj V)) _ _ T
    (((l.operation.pushforward.map (t.app M)).val.app W)
      ((l.operation.moduleAdjunction.unit.app (M.over V)).val.app W x))
    (((l.operation.pushforward.map (t.app N)).val.app W)
      ((l.operation.moduleAdjunction.unit.app (N.over V)).val.app W y)) at hmap
  rw [hM, hN] at hmap
  change ((l.restrictionX.ordinaryTensor (g.operation.pullback.obj M)
      (g.operation.pullback.obj N)).hom.val.app T)
      (((g.operation.pushforward.map (g.ordinaryTensor.iso M N).hom).val.app
        (op W.unop.left))
        (((l.operation.pushforward.map (t.app (((tensor R_Y).obj M).obj N))).val.app W)
          ((l.operation.moduleAdjunction.unit.app _).val.app W
            (((l.restrictionY.ordinaryTensor M N).inv.val.app W)
              (pure (R_Y.over V) (M.over V) (N.over V) W x y))))) =
    (((Functor.uncurry.obj (tensor (R_X.over ((proEtaleBaseChange f).obj V)))).map
      (Prod.mkHom (t.app M) (t.app N))).val.app T)
      (((l.operation.pushforward.map
          (l.ordinaryTensor.iso (M.over V) (N.over V)).hom).val.app W)
        (((l.operation.pushforward.map
          (l.operation.pullback.map (l.restrictionY.ordinaryTensor M N).hom)).val.app W)
          ((l.operation.moduleAdjunction.unit.app _).val.app W
            (((l.restrictionY.ordinaryTensor M N).inv.val.app W)
              (pure (R_Y.over V) (M.over V) (N.over V) W x y)))))
  rw [hback, hTensor, ← hu, g.ordinaryTensor.pure_unit, l.ordinaryTensor.pure_unit]
  exact (l.restrictionX.pure_sections _ _ T _ _).trans hmap.symm

end AlgebraicGeometry.Scheme.ProjectionRestriction
