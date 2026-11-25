/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteUnit
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Integral generator homomorphism bijection for finite coefficients.
(blueprint: lem-sfb-finite-quotient-hom-bijective). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def finiteTerminalSectionsEquiv (T : Scheme.{u}) (n : ℕ)
    (M : SheafOfModules.{u + 1}
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))) :
    M.sections ≃ M.val.obj (op (Scheme.ProEt.mk (𝟙 T))) where
  toFun s := s.val _
  invFun x := M.val.sectionsMk
    (fun W ↦ M.val.map ((Scheme.ProEt.isTerminalMkId T).from W.unop).op x)
    (by
      intro W V f
      rw [← PresheafOfModules.map_comp_apply]
      have h : ((Scheme.ProEt.isTerminalMkId T).from W.unop).op ≫ f =
          ((Scheme.ProEt.isTerminalMkId T).from V.unop).op := by
        apply Quiver.Hom.unop_inj
        apply (Scheme.ProEt.isTerminalMkId T).hom_ext
      rw [h])
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro W
    exact PresheafOfModules.sections_property s _
  right_inv x := by
    change M.val.map ((Scheme.ProEt.isTerminalMkId T).from _).op x = x
    have h : (Scheme.ProEt.isTerminalMkId T).from (Scheme.ProEt.mk (𝟙 T)) = 𝟙 _ :=
      (Scheme.ProEt.isTerminalMkId T).hom_ext _ _
    rw [h]
    simp

private def finiteModuleHomEquiv (T : Scheme.{u}) (n : ℕ)
    (M : SheafOfModules.{u + 1}
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))) :
    (((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T))) ⟶ M) ≃
      M.val.obj (op (Scheme.ProEt.mk (𝟙 T))) :=
  (Iso.homCongr (coefficientEvaluationUnit l E T n).symm (Iso.refl M)).trans
    (M.unitHomEquiv.trans (finiteTerminalSectionsEquiv l E T n M))

private theorem finiteModuleHomEquiv_apply (T : Scheme.{u}) (n : ℕ)
    (M : SheafOfModules.{u + 1}
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n)))
    (f : (SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)) ⟶ M) :
    finiteModuleHomEquiv l E T n M f =
      f.val.app (op (Scheme.ProEt.mk (𝟙 T)))
        ((coefficientEvaluationUnit l E T n).hom.val.app (op (Scheme.ProEt.mk (𝟙 T)))
          (1 : (SpTowerShriek.B l E T n).obj.obj (op (Scheme.ProEt.mk (𝟙 T))))) := by
  simp only [finiteModuleHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]
  rfl

private def finiteAbelianHomEquiv (T : Scheme.{u}) (M : DiagonalAb T) :
    ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ M) ≃
        M.obj.obj (op (Scheme.ProEt.mk (𝟙 T))) :=
  ((constantSheafAdj (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.isTerminalMkId T)).homEquiv _ _).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

theorem finiteQuotient_hom_bijective (T : Scheme.{u}) (n : ℕ)
    (M : SheafOfModules.{u + 1}
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))) :
    Function.Bijective (fun f :
      (SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)) ⟶ M ↦
        finiteQuotient l E T n ≫ (finiteForget l E T n).map f) := by
  let e := finiteAbelianHomEquiv T ((finiteForget l E T n).obj M)
  have h : e ∘ (fun f :
      (SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)) ⟶ M ↦
        finiteQuotient l E T n ≫ (finiteForget l E T n).map f) =
      finiteModuleHomEquiv l E T n M := by
    funext f
    dsimp only [Function.comp_apply, e, finiteAbelianHomEquiv, Equiv.trans_apply,
      AddEquiv.toEquiv_eq_coe]
    erw [AddCommGrpCat.uliftZMultiplesAddEquiv_eq]
    erw [AlgebraicGeometry.constantSheafAdj_homEquiv_eq]
    rw [finiteModuleHomEquiv_apply]
    let q := finiteQuotient l E T n
    change f.val.app _ (q.hom.app _
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app _ ⟨1⟩)) =
      f.val.app (op (Scheme.ProEt.mk (𝟙 T)))
        ((coefficientEvaluationUnit l E T n).hom.val.app (op (Scheme.ProEt.mk (𝟙 T)))
          (1 : (SpTowerShriek.B l E T n).obj.obj (op (Scheme.ProEt.mk (𝟙 T)))))
    have hq1 : HEq (q.hom.app (op (Scheme.ProEt.mk (𝟙 T)))
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app _ ⟨1⟩))
        (1 : (SpTowerShriek.B l E T n).obj.obj (op (Scheme.ProEt.mk (𝟙 T)))) := by
      have hq0 := (finiteQuotient_existsUnique l E T n).exists.choose_spec
        (op (Scheme.ProEt.mk (𝟙 T))) (⟨1⟩ : ULift.{u + 1} ℤ)
      convert hq0 using 1
      · rfl
      · simp only [Int.cast_one]
    have hu := coefficientEvaluationUnit_sections l E T n
      (op (Scheme.ProEt.mk (𝟙 T)))
      (1 : (SpTowerShriek.B l E T n).obj.obj (op (Scheme.ProEt.mk (𝟙 T))))
    exact congrArg (fun z ↦ f.val.app (op (Scheme.ProEt.mk (𝟙 T))) z)
      (eq_of_heq (hq1.trans hu.symm))
  have hb := h ▸ (finiteModuleHomEquiv l E T n M).bijective
  exact Function.Bijective.of_comp_left hb e.injective

end AlgebraicGeometry.ProEtale.DiagonalTrace
