/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteInjectiveSectionsAcyclic
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteQuotientHomBijective
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteDerivedRestrictionBijective
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
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived

/-! # Detection of finite coefficient classes on the integral generator

Source: diagonal-tower trace (1), scalar Kummer normalization; the constant-module
class comparison in Stacks 03FD.
(blueprint: lem-sfb-finite-quotient-derived-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u uA vA uB vB wA wB wDA wDB
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem restrictionArrows_injective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B] [EnoughInjectives A]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {F : B} {P : A} (η : F ⟶ U.obj P)
    (hzero : ∀ M : A, Function.Bijective (fun f : P ⟶ M ↦ η ≫ U.map f))
    (hacyc : ∀ (I : A) [Injective I] (q : ℕ),
      Subsingleton (Ext.{wB} F (U.obj I) (q + 1))) (q : ℕ) (M : A) :
    Function.Injective (fun a :
      (DerivedCategory.singleFunctor A 0).obj P ⟶
        ((DerivedCategory.singleFunctor A 0).obj M)⟦(q : ℤ)⟧ ↦
      (DerivedCategory.singleFunctor B 0).map η ≫ mapSingleArrow U (q : ℤ) a) := by
  intro a b hab
  apply Ext.homEquiv.symm.injective
  apply (restrictionClass_bijective U η hzero hacyc q M).1
  apply Ext.homEquiv.injective
  change ((Ext.mk₀ η).comp ((Ext.homEquiv.symm a).mapExactFunctor U)
      (zero_add q)).hom =
    ((Ext.mk₀ η).comp ((Ext.homEquiv.symm b).mapExactFunctor U) (zero_add q)).hom
  simpa only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    Ext.mapExactFunctor_hom, ShiftedHom.map, mapSingleArrow, Ext.hom,
    Equiv.apply_symm_apply, Category.assoc] using hab

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Forgetting coefficients and evaluating on the integral generator detects derived
arrows out of the regular finite coefficient sheaf, with any finite-module target.

Source: diagonal-tower trace (1), constants/scalar-extension adjunction; Stacks 03FD.
(blueprint: lem-sfb-finite-quotient-derived-detection).

Proof: the evaluated coefficient object is the regular module over the constant
finite coefficient ring sheaf. Maps from it are global sections by evaluation at
one. Maps from the integral constant sheaf to an underlying abelian sheaf are
also global sections by evaluation at one. The characterization of finiteQuotient
identifies these degree-zero comparisons. Resolve the target by injective module
sheaves. Their underlying abelian sheaves are acyclic for global sections,
by the injective-module resolution computation of underlying sheaf cohomology
in Stacks 03FD. This computation applies to a ringed site, and requires no
flatness of the coefficient ring as an abelian group. It identifies the two
universal delta functors, rather than asserting that the forgetful functor
preserves injectives. Dimension shifting extends the degree-zero identification to
every degree. The exact forgetful functor and its single and shift comparisons
identify the degree-two comparison with the displayed map. It is therefore
injective. This uses no projective-line decomposition, no Chern class, and no
chosen line comparison. For the empty scheme or the zero coefficient ring all
maps in question are the unique maps, so the conclusion still holds. -/
theorem finiteQuotient_detects_derived_arrows (T : Scheme.{u}) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (M : SheafOfModules.{u + 1}
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))) :
    Function.Injective (fun a :
      (DerivedCategory.singleFunctor _ 0).obj
          ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T))) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧ ↦
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n) ≫
        mapSingleArrow (finiteForget l E T n) (2 : ℤ) a) := by
  let R := SemilinearSections.ring.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n)
  have : EnoughInjectives (SheafOfModules.{u + 1} R) := by
    let : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} R) :=
      SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
    infer_instance
  let : HasExt.{u + 1} (SheafOfModules.{u + 1} R) := hasExt_of_enoughInjectives _
  let : HasExt.{u + 1} (DiagonalAb T) := hasExt_of_enoughInjectives _
  have hacyc (I : SheafOfModules.{u + 1} R) [Injective I] (q : ℕ) :
      Subsingleton (Ext.{u + 1} ((abEvaluation T n).obj (integers T))
        ((finiteForget l E T n).obj I) (q + 1)) := by
    apply (Sheaf.subsingleton_H_iff_isZero_rightDerived (Scheme.ProEt.topology T)
      (Scheme.ProEt.isTerminalMkId T) (q + 1) ((finiteForget l E T n).obj I)).mpr
    exact finiteInjective_sections_acyclic l E T n I q
  exact restrictionArrows_injective (finiteForget l E T n) (finiteQuotient l E T n)
    (finiteQuotient_hom_bijective l E T n) hacyc 2 M

end AlgebraicGeometry.ProEtale.DiagonalTrace
