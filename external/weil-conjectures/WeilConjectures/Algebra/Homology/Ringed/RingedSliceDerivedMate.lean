/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedSliceData
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceDerivedAdjunction
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree

/-!
# Invertibility of the derived slice mate

Source: Stacks Project, algebraization.tex, Tag 099J; Modules on Sites, Tag 04J0;
Cohomology on Sites, Tag 07A6
(blueprint: lem-weil-pbc-ringed-slice-derived-mate-isIso).
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

attribute [local instance 20000] CategoryTheory.siteAbelianHasSheafify
  CategoryTheory.siteAbelianWEqualsLocallyBijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 20000 in
-- The generic mate identity needs only a small fixed elaboration budget.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryUnit
    {A B Av Bv : Type*} [Category A] [Category B] [Category Av] [Category Bv]
    {G : A ⥤ B} {F : B ⥤ A} {Gv : Av ⥤ Bv} {Fv : Bv ⥤ Av}
    (adj : G ⊣ F) (adjv : Gv ⊣ Fv) (rA : A ⥤ Av) (rB : B ⥤ Bv)
    (lam : rA ⋙ Gv ≅ G ⋙ rB) (b : F ⋙ rA ≅ rB ⋙ Fv)
    (ht : ∀ (M : A) (N : B) (h : M ⟶ F.obj N),
      lam.hom.app M ≫ rB.map ((adj.homEquiv M N).symm h) =
        (adjv.homEquiv _ _).symm (rA.map h ≫ b.hom.app N)) (P : A) :
    adjv.homEquiv _ _ (lam.hom.app P) =
      rA.map (adj.unit.app P) ≫ b.hom.app (G.obj P) := by
  apply (adjv.homEquiv _ _).symm.injective
  have hh := ht P (G.obj P) (adj.unit.app P)
  rw [Adjunction.homEquiv_symm_unit] at hh
  rw [rB.map_id] at hh
  erw [Category.comp_id] at hh
  dsimp only [Functor.comp_obj] at hh ⊢
  simpa only [Equiv.symm_apply_apply] using hh

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

end SheafOfModules
