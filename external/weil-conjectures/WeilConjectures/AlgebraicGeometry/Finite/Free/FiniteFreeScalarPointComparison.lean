/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.WeilObject.Sheaf.StalkUnit
/-! # The underlying sheaf map of point module composition
(blueprint: new-sfb-finite-free-scalar-point-comparison)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open CondensedRing
attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] upperStarFromPoint Mod.extendScalarsIsoComapInv
private lemma unitComparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [BraidedCategory E] [HasCoequalizers E]
    [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (τ : F ⋙ G ⟶ H) [NatTrans.IsMonoidal τ] [IsIso τ]
    (R : C) [MonObj R] [IsCommMonObj (G.obj (F.obj R))]
    [IsIso (Functor.compAlgHom F G τ R)]
    (e : F.mapMod R ⋙ G.mapMod (F.obj R) ⋙
      Mod.extendScalars (Functor.compAlgHom F G τ R) ≅ H.mapMod R)
    (he : e = Functor.mapModCompExtendScalarsIso F G τ R) (M : Mod C R) :
    Mod.extendUnitHom (Functor.compAlgHom F G τ R)
        ((G.mapMod (F.obj R)).obj ((F.mapMod R).obj M)) ≫
      (e.hom.app M).hom = τ.app M.X := by
  subst he
  exact Functor.extendUnitHom_mapModCompExtendScalarsIso_hom_app_hom F G τ R M

-- Compute the point comparison on its explicit module-composition model.
/-- The canonical point module comparison has the specified underlying sheaf map.
Source: blueprint scalar-six formal properties, p_X = f* p_Y.
(blueprint: new-sfb-finite-free-scalar-point-comparison)

Proof. Identify the inverse underlying scalar-extension map with its extension unit.
The generic module-composition unit formula then computes the point comparison.
The proof covers all coefficient modules, including zero modules. -/
theorem finiteFreeScalar_pointComparison_underlying
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R) :
    (profinitePointModuleForgetPullbackIso R f).inv.app
        ((CondensedRing.upperStarFromPointMod R Y).obj M) ≫
      ((Functor.mapModCompExtendScalarsIso (upperStarFromPoint Y)
        (ProEtale.upperStar Ab.{u + 1} f) (upperStarFromPointComp f).hom R).hom.app M).hom =
      (upperStarFromPointComp f).hom.app M.X := by
  let φ := condensedPullbackHom R f
  let N := ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj R Y)).obj
    ((CondensedRing.upperStarFromPointMod R Y).obj M)
  have hu : Mod.extendUnitHom φ N =
      ((Mod.extendScalarsIsoComapInv φ).inv.app N).hom := by
    apply (cancel_mono ((Mod.extendScalarsIsoComapInv φ).hom.app N).hom).1
    rw [Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app]
    rw [← Mod.comp_hom', Iso.inv_hom_id_app, Mod.id_hom']
    rfl
  change ((Mod.extendScalarsIsoComapInv φ).inv.app N).hom ≫ _ = _
  rw [← hu]
  exact unitComparison (upperStarFromPoint Y) (ProEtale.upperStar Ab.{u + 1} f)
    (upperStarFromPointComp f).hom R
    (Functor.mapModCompExtendScalarsIso (upperStarFromPoint Y)
      (ProEtale.upperStar Ab.{u + 1} f) (upperStarFromPointComp f).hom R) rfl M

end AlgebraicGeometry.ProEtale
