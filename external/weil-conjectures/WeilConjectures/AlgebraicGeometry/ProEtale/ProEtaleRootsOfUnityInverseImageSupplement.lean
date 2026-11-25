/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
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
public import WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage

/-! # Inverse-image comparison for pro-etale roots of unity

## Main definitions

- `proEtaleRootsOfUnityDirectImageMap`: pullback of roots along the projection.
- `proEtaleRootsOfUnityInverseImageMap`: its inverse-image adjunct.

## References

* Stacks Project, Tag 03PK
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem sections_inclusion (S : Scheme.{u}) (N : ℕ) (U : S.ProEtᵒᵖ)
    (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    ULift.up (Additive.ofMul (Additive.toMul
      (proEtaleRootsOfUnitySections S N U x)).val) =
      (proEtaleRootsOfUnityInclusion S N).hom.app U x := by
  exact (existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose_spec x

private theorem sections_map (S : Scheme.{u}) (N : ℕ) {U V : S.ProEtᵒᵖ}
    (a : U ⟶ V) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    proEtaleRootsOfUnitySections S N V ((proEtaleRootsOfUnitySheaf S N).obj.map a x) =
      Additive.ofMul (restrictRootsOfUnity a.unop.left.appTop.hom N
        (Additive.toMul (proEtaleRootsOfUnitySections S N U x))) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  have h := congrArg (fun b ↦ b x) ((proEtaleRootsOfUnityInclusion S N).hom.naturality a)
  change (proEtaleRootsOfUnityInclusion S N).hom.app V
      ((proEtaleRootsOfUnitySheaf S N).obj.map a x) =
    (proEtaleUnitsSheaf S).obj.map a
      ((proEtaleRootsOfUnityInclusion S N).hom.app U x) at h
  rw [← sections_inclusion, ← sections_inclusion] at h
  exact congrArg (fun y ↦ y.down.toMul) h

/-- Naturality of the sectionwise projection formula.
The pullback projection square commutes, and global sections turn this commutative
square into the equality of ring maps used below. -/
private theorem proEtaleRootsOfUnityDirectImageNaturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    ∀ (U V : Y.ProEtᵒᵖ) (a : U ⟶ V),
      ((proEtaleRootsOfUnitySheaf Y N).obj.map a ≫
        AddCommGrpCat.ofHom
          ((proEtaleRootsOfUnitySections X N
              ((proEtaleBaseChange f).op.obj V)).symm.toAddMonoidHom.comp
            ((restrictRootsOfUnity (pullback.fst V.unop.hom f).appTop.hom N).toAdditive.comp
              (proEtaleRootsOfUnitySections Y N V).toAddMonoidHom))) =
      AddCommGrpCat.ofHom
          ((proEtaleRootsOfUnitySections X N
              ((proEtaleBaseChange f).op.obj U)).symm.toAddMonoidHom.comp
            ((restrictRootsOfUnity (pullback.fst U.unop.hom f).appTop.hom N).toAdditive.comp
              (proEtaleRootsOfUnitySections Y N U).toAddMonoidHom)) ≫
        ((proEtaleBaseChange f).op ⋙ (proEtaleRootsOfUnitySheaf X N).obj).map a := by
  intro U V a
  let r (W : Y.ProEtᵒᵖ) :=
    (restrictRootsOfUnity (pullback.fst W.unop.hom f).appTop.hom N).toAdditive
  let eY (W : Y.ProEtᵒᵖ) := proEtaleRootsOfUnitySections Y N W
  let eX (W : Y.ProEtᵒᵖ) :=
    proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj W)
  let a' := (proEtaleBaseChange f).op.map a
  have hproj : ((proEtaleBaseChange f).map a.unop).left ≫
      pullback.fst U.unop.hom f =
      pullback.fst V.unop.hom f ≫ a.unop.left := by
    exact pullback.lift_fst _ _ _
  have hr (y : Additive (rootsOfUnity N ((proEtaleStructureSheaf Y).obj.obj U))) :
      r V (Additive.ofMul (restrictRootsOfUnity a.unop.left.appTop.hom N y.toMul)) =
        Additive.ofMul (restrictRootsOfUnity a'.unop.left.appTop.hom N
          ((r U y).toMul)) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    have h := congrArg (fun g ↦ g.appTop) hproj
    simp only [Hom.comp_appTop] at h
    exact congrArg (fun g ↦ g.hom y.toMul.val.val) h.symm
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change (eX V).symm (r V (eY V ((proEtaleRootsOfUnitySheaf Y N).obj.map a x))) =
    (proEtaleRootsOfUnitySheaf X N).obj.map a' ((eX U).symm (r U (eY U x)))
  apply (eX V).injective
  calc
    _ = r V (eY V ((proEtaleRootsOfUnitySheaf Y N).obj.map a x)) :=
      (eX V).apply_symm_apply _
    _ = r V (Additive.ofMul (restrictRootsOfUnity a.unop.left.appTop.hom N
        (Additive.toMul (eY U x)))) := congrArg (r V) (sections_map Y N a x)
    _ = Additive.ofMul (restrictRootsOfUnity a'.unop.left.appTop.hom N
        (Additive.toMul (r U (eY U x)))) := hr (eY U x)
    _ = _ := by
      have h := sections_map X N a' ((eX U).symm (r U (eY U x)))
      exact ((congrArg (fun y ↦ Additive.ofMul
        (restrictRootsOfUnity a'.unop.left.appTop.hom N (Additive.toMul y)))
        ((eX U).apply_symm_apply (r U (eY U x)))).symm.trans h.symm)

/-- The comparison `c` is the adjoint of `β`, using the recorded inverse-image adjunction. -/
noncomputable def proEtaleRootsOfUnityInverseImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N) ⟶ proEtaleRootsOfUnitySheaf X N :=
  ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (proEtaleRootsOfUnityDirectImageMap f N)

end AlgebraicGeometry.Scheme
