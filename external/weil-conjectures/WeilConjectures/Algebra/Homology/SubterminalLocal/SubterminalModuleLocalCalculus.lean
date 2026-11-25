/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteNestedExtensionMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Local calculus of module sheaves on two covering subterminals

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ and 0F6Z; Sites,
Tag 04B8 (blueprint: lem-sp-subterminal-module-local-calculus).

## Main definitions

* `Intersection`: the module-linear comparisons with their adjunction normalizations.
* `JointDetection`: the zero, exactness, cohomology and quasi-isomorphism tests.
* `nested` is imported from `SiteNestedExtensionMap`, its definition-node module.

## Main statements

* `subterminal_module_local_calculus`: the full calculus for a binary subterminal cover.
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r a b ha hb wa wb w s
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SubterminalLocal

/-- The recorded module sheafification with identity coefficient map.
Source: Stacks 03DI (blueprint: lem-sp-subterminal-module-local-calculus). -/
abbrev sheafify {D : Type a} [Category.{ha} D] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{s}] [K.WEqualsLocallyBijective AddCommGrpCat.{s}]
    (S : Sheaf K RingCat.{s}) :=
  PresheafOfModules.sheafification.{s, ha, s, a}
    (J := K) (R := S) (R₀ := S.obj) (𝟙 S.obj)

variable {C : Type c} [Category.{v} C] [HasFiniteLimits C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

section LocalCalculusProof
set_option backward.defeqAttrib.useBackward true

section SheafificationComparison

open PresheafOfModules
variable {D : Type a} [Category.{ha} D] {E : Type b} [Category.{hb} E]
  {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [HasSheafify K AddCommGrpCat.{s}] [K.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify L AddCommGrpCat.{s}] [L.WEqualsLocallyBijective AddCommGrpCat.{s}]
  (F : D ⥤ E) [F.IsContinuous K L] [F.IsCocontinuous K L]
  (S : Sheaf L RingCat.{s})

private def restrictedRing : Sheaf K RingCat.{s} :=
  (F.sheafPushforwardContinuous RingCat.{s} K L).obj S

private def restrictionP : PresheafOfModules.{s} S.obj ⥤
    PresheafOfModules.{s} (restrictedRing (K := K) F S).obj :=
  PresheafOfModules.pushforward (F := F) (𝟙 _)

private def restrictionS : SheafOfModules.{s} S ⥤
    SheafOfModules.{s} (restrictedRing (K := K) F S) :=
  SheafOfModules.pushforward (F := F) (𝟙 _)

private def restrictionUnit (M : PresheafOfModules.{s} S.obj) :
    (restrictionP (K := K) F S).obj M ⟶
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 (restrictedRing (K := K) F
        S).obj)).obj
        ((restrictionS (K := K) F S).obj
          ((PresheafOfModules.sheafification.{s} (J := L) (R := S) (R₀ := S.obj) (𝟙 S.obj)).obj
            M)) :=
  (restrictionP (K := K) F S).map
    ((PresheafOfModules.sheafificationAdjunction (J := L) (R := S) (𝟙 S.obj)).unit.app M)

omit [HasSheafify K AddCommGrpCat.{s}] in
private theorem restrictionUnit_W (M : PresheafOfModules.{s} S.obj) :
    K.W ((PresheafOfModules.toPresheaf _).map (restrictionUnit (K := K) F S M)) := by
  let η := CategoryTheory.toSheafify L M.presheaf
  change K.W (Functor.whiskerLeft F.op η)
  have : Presheaf.IsLocallyInjective K (Functor.whiskerLeft F.op η) :=
    Presheaf.isLocallyInjective_whisker K L F η
  have : Presheaf.IsLocallySurjective K (Functor.whiskerLeft F.op η) :=
    Presheaf.isLocallySurjective_whisker K L F η
  exact K.W_of_isLocallyBijective _

end SheafificationComparison

omit [HasFiniteLimits C] in
open Classical in
private theorem extensionRestrict_of
    (Z : C) (F : SliceModules.{c, v, r} R Z) {X Y : Cᵒᵖ} (a : X ⟶ Y)
    (φ : X.unop ⟶ Z) (ψ : Y.unop ⟶ Z) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd (coefficients.{c, v, r} R) Z F a
        (DirectSum.of (fun b : X.unop ⟶ Z ↦ F.val.obj (op (Over.mk b))) φ x) =
      DirectSum.of (fun b : Y.unop ⟶ Z ↦ F.val.obj (op (Over.mk b))) ψ (F.val.map
        (op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  classical
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun b : X.unop ⟶ Z ↦ F.val.obj (op (Over.mk b))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

open Classical in
private def singletonInclusion (Z : C) (F : SliceModules.{c, v, r} R Z) :
    F.val ⟶ (restrictionP (Over.forget Z) (coefficients.{c, v, r} R)).obj
      ((extensionByZeroPresheaf (coefficients.{c, v, r} R) Z).obj F) where
  app X := ModuleCat.ofHom (DirectSum.lof _ _
    (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom)
  naturality {X Y} f := by
    ext x
    change DirectSum.of (fun b : Y.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b)))
      Y.unop.hom (F.val.map f x) =
      extensionByZeroPresheafRestrictAdd (coefficients.{c, v, r} R) Z F
        ((Over.forget Z).op.map f)
        (DirectSum.of (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom x)
    have hr := extensionRestrict_of.{c, v, r} R Z F ((Over.forget Z).op.map f)
      X.unop.hom Y.unop.hom (Over.w f.unop) x
    have hf : (Over.homMk f.unop.left (Over.w f.unop) : Y.unop ⟶ X.unop) =
        f.unop := by ext; rfl
    erw [hf] at hr
    exact hr.symm

private theorem singletonInclusion_isIso (Z : C) [Mono (terminal.from Z)]
    (F : SliceModules.{c, v, r} R Z) : IsIso (singletonInclusion.{c, v, r} R Z F) := by
  classical
  have hcomp : ∀ X, IsIso ((singletonInclusion.{c, v, r} R Z F).app X) := by
    intro X
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · change Function.Injective
        (DirectSum.of (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom)
      exact DirectSum.of_injective
        (β := fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom
    · intro x
      refine ⟨DirectSum.component ((coefficients.{c, v, r} R).obj.obj (op X.unop.left)) _
        (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom x, ?_⟩
      change DirectSum.of (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b)))
        X.unop.hom (DirectSum.component ((coefficients.{c, v, r} R).obj.obj (op X.unop.left)) _
          (fun b : X.unop.left ⟶ Z ↦ F.val.obj (op (Over.mk b))) X.unop.hom x) = x
      apply DirectSum.ext
      intro a
      have ha : a = X.unop.hom := by
        apply (cancel_mono (terminal.from Z)).1
        subsingleton
      subst a
      exact DFinsupp.single_eq_same
  let e := PresheafOfModules.isoMk
    (fun X ↦ asIso ((singletonInclusion.{c, v, r} R Z F).app X))
    (fun {X Y} f ↦ (singletonInclusion.{c, v, r} R Z F).naturality f)
  exact e.isIso_hom

private theorem adj_unit_isIso (Z : C) [Mono (terminal.from Z)] :
    IsIso (adj.{c, v, r} R Z).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have hi := singletonInclusion_isIso.{c, v, r} R Z F
  let η := restrictionUnit (K := J.over Z) (Over.forget Z) (coefficients.{c, v, r} R)
    ((extensionByZeroPresheaf (coefficients.{c, v, r} R) Z).obj F)
  have heq : ((adj.{c, v, r} R Z).unit.app F).val =
      singletonInclusion.{c, v, r} R Z F ≫ η := by
    ext X x
    exact (localizedSystemAdjunction_existsUnique.{c, v, r} R Z).exists.choose_spec F X x
  apply (isIso_iff_of_reflects_iso _ (toSheaf ((coefficients.{c, v, r} R).over Z))).1
  apply ((J.over Z).W_sheafToPresheaf_map_iff_isIso _).1
  change (J.over Z).W ((PresheafOfModules.toPresheaf _).map
    ((adj.{c, v, r} R Z).unit.app F).val)
  rw [heq, CategoryTheory.Functor.map_comp]
  apply (J.over Z).W.comp_mem _ _
  · exact (J.over Z).W.of_isIso _
  · exact restrictionUnit_W (Over.forget Z) (coefficients.{c, v, r} R) _

private def sliceExtension {A B : C} (_f : A ⟶ B) :
    SliceModules.{c, v, r} R A ⥤ SliceModules.{c, v, r} R B :=
  jbang.{c, v, r} R A ⋙ jstar.{c, v, r} R B

private def restrictionSquare {U V W : C} (f : W ⟶ U) (g : W ⟶ V) :
    TwoSquare (jstar.{c, v, r} R V) (jstar.{c, v, r} R U)
      (overMap.{max c v r} (coefficients.{c, v, r} R) g)
      (overMap.{max c v r} (coefficients.{c, v, r} R) f) :=
  (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) g).hom ≫
    (overFunctorMap.{max c v r} (coefficients.{c, v, r} R) f).inv

end LocalCalculusProof

end SheafOfModules.SubterminalLocal
