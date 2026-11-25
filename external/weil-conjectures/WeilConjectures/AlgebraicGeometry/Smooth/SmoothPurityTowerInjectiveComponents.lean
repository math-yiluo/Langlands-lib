/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerEvaluationAdjoint
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
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Acyclic components of injective coefficient towers

Source: blueprint main-20261015, chap-Smooth-purity, prose-09-23,
`sk-lem-sp-tower-levels-acyclic.md` and its proof; Stacks Tags 03FD, 015E and 05TH
(blueprint: prose-09-23).

Index n denotes the positive level n+1. The tower direct image is the actual
product-site module pushforward. Its scalar map is the existing constant-section
map, so both coefficients and transitions are fixed, including for the identity map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {T S : Scheme.{t}} (g : T ⟶ S)

private theorem presheafPushforward_finiteLimits.{v, w, v₁, w₁, v₂, w₂}
    {C : Type w₁} [Category.{v₁} C] {D : Type w₂} [Category.{v₂} D]
    (F : C ⥤ D) {R : Dᵒᵖ ⥤ RingCat.{w}} {S : Cᵒᵖ ⥤ RingCat.{w}}
    (φ : S ⟶ F.op ⋙ R) :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{v} φ) := by
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
    isLimitOfPreserves
      (PresheafOfModules.evaluation R (F.op.obj X) ⋙
        ModuleCat.restrictScalars (φ.app X).hom) hc)⟩

private theorem moduleHom_fun_heq.{v, w} {R : Type w} [Ring R]
    {M M' N N' : ModuleCat.{v} R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {f' : M' ⟶ N'} (h : HEq f f') :
    HEq (fun x ↦ f x) (fun x ↦ f' x) := by
  subst M'
  subst N'
  cases h
  rfl

private theorem pushforward_restriction_fun_heq.{v, w, v₁, w₁, v₂, w₂}
    {C : Type w₁} [Category.{v₁} C] {D : Type w₂} [Category.{v₂} D]
    (F : C ⥤ D) {R : (ℕ × D)ᵒᵖ ⥤ RingCat.{w}}
    {S : (ℕ × C)ᵒᵖ ⥤ RingCat.{w}}
    (φ : S ⟶ ((𝟭 ℕ).prod F).op ⋙ R) (M : PresheafOfModules.{v} R)
    (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    HEq (fun x ↦ ((PresheafOfModules.pushforward φ).obj M).map
      (Prod.mkHom (𝟙 n) f.unop).op x)
      (fun x ↦ M.map (Prod.mkHom (𝟙 n) (F.op.map f).unop).op x) := by
  rfl

private theorem moduleRestriction_naturality.{v, w} {R S : Type w} [Ring R] [Ring S]
    (φ : R →+* S) {M M' : ModuleCat.{v} R} {N N' : ModuleCat.{v} S}
    (hM : M = M') (hN : N = N')
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (f' : M' ⟶ (ModuleCat.restrictScalars φ).obj N')
    (h : HEq (fun x ↦ f x) (fun x ↦ f' x)) :
    f ≫ (ModuleCat.restrictScalars φ).map (eqToHom hN) = eqToHom hM ≫ f' := by
  subst M'
  subst N'
  ext x
  exact congrFun (eq_of_heq h) x

private theorem moduleHom_naturality.{v, w} {R : Type w} [Ring R]
    {M M' N N' : ModuleCat.{v} R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (f' : M' ⟶ N')
    (h : HEq (fun x ↦ f x) (fun x ↦ f' x)) :
    f ≫ eqToHom hN = eqToHom hM ≫ f' := by
  subst M'
  subst N'
  ext x
  exact congrFun (eq_of_heq h) x

private theorem moduleEqToHom_apply_heq.{v, w} {R : Type w} [Ring R]
    {M N : ModuleCat.{v} R} (h : M = N) (x : M) : HEq (eqToHom h x) x := by
  subst N
  rfl

variable (dT : SpCoefficientTowersAbelian l E T) (dS : SpCoefficientTowersAbelian l E S)

private theorem moduleSheafIso_unique.{v, w, v₁, w₁, v₂, w₂}
    {A : Type w₁} [Category.{v₁} A] {C : Type w₂} [Category.{v₂} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (F G : A ⥤ SheafOfModules.{v} R) (e : F ≅ G)
    (he : ∀ (M : A) (U : Cᵒᵖ) (x : (F.obj M).val.obj U),
      HEq ((e.hom.app M).val.app U x) x) :
    ∃! e' : F ≅ G, ∀ (M : A) (U : Cᵒᵖ) (x : (F.obj M).val.obj U),
      HEq ((e'.hom.app M).val.app U x) x := by
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M U x
  exact eq_of_heq ((he' M U x).trans (he M U x).symm)

private theorem small_module_evaluation_additive.{w} {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    (SheafOfModules.evaluation.{w} R U).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] small_module_evaluation_additive

private def supportedProductIso.{v, w} {C : Type w} [Category.{v} C]
    [HasZeroMorphisms C] {X : ℕ → C} (P : Fan X) (hP : IsLimit P) (r : ℕ)
    [HasProduct (fun n : Fin (r + 1) ↦ X n.val)]
    (hz : ∀ n : ℕ, r < n → IsZero (X n)) :
    P.pt ≅ ∏ᶜ fun n : Fin (r + 1) ↦ X n.val := by
  classical
  let f : (n : ℕ) → (∏ᶜ fun n : Fin (r + 1) ↦ X n.val) ⟶ X n := fun n ↦
    if h : n < r + 1 then Pi.π (fun n : Fin (r + 1) ↦ X n.val) ⟨n, h⟩ else 0
  let Q := Fan.mk (∏ᶜ fun n : Fin (r + 1) ↦ X n.val) f
  refine
    { hom := Pi.lift (fun n ↦ P.proj n.val)
      inv := hP.lift Q
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply hP.hom_ext
    intro ⟨n⟩
    rw [Category.assoc, hP.fac Q]
    by_cases hn : n < r + 1
    · simpa only [Q, Fan.mk_π_app, f, dite_eq_left hn, Category.id_comp, Fan.proj] using
        Pi.lift_comp_π (fun n : Fin (r + 1) ↦ P.proj n.val) ⟨n, hn⟩
    · exact (hz n (by omega)).eq_of_tgt _ _
  · apply Pi.hom_ext
    intro n
    rw [Category.assoc, Pi.lift_comp_π]
    simpa only [Q, Fan.mk_π_app, f, dite_eq_left n.isLt, Category.id_comp, Fan.proj, Fin.eta] using
      hP.fac Q ⟨n.val⟩

private theorem evaluatedProductRetract.{v, w, v', w'}
    {A : Type w} [Category.{v} A] {B : Type w'} [Category.{v'} B]
    [HasZeroMorphisms B] (V : A ⥤ B) [PreservesLimitsOfShape (Discrete ℕ) V]
    {X : ℕ → A} (P : Fan X) (hP : IsLimit P) {I : A} (s : Retract I P.pt)
    (r : ℕ) [HasProduct (fun n : Fin (r + 1) ↦ V.obj (X n.val))]
    (hz : ∀ n : ℕ, r < n → IsZero (V.obj (X n))) :
    Nonempty (Retract (V.obj I) (∏ᶜ fun n : Fin (r + 1) ↦ V.obj (X n.val))) := by
  let Q : Fan (fun n ↦ V.obj (X n)) := Fan.mk (V.obj P.pt) (fun n ↦ V.map (P.proj n))
  have hQ : IsLimit Q :=
    isLimitFanMkObjOfIsLimit V _ _
      (IsLimit.ofIsoLimit hP (Cone.ext (Iso.refl _) (by intro ⟨n⟩; simp [Fan.proj])))
  exact ⟨(s.map V).trans (Retract.ofIso (supportedProductIso Q hQ r hz))⟩


private theorem acyclic_of_finite_product_retract.{v, w, v', w'}
    {C : Type w} [Category.{v} C] {D : Type w'} [Category.{v'} D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {N : Type} [Finite N] (J : N → C)
    {I : C} (s : Retract I (∏ᶜ J)) (hJ : ∀ n, F.rightAcyclic (J n)) :
    F.rightAcyclic I := by
  let : F.rightAcyclic.IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  have hP := F.rightAcyclic.prop_product hJ
  intro q
  have h := s.map (F.rightDerived (q + 1))
  exact IsZero.of_mono h.i (hP q)

private theorem small_forgotten_injective_acyclic.{w}
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{w}) (U : C) (I : SheafOfModules.{w} R) [Injective I] :
    (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)).rightAcyclic
        ((SheafOfModules.toSheaf R).obj I) := by
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{w} J AddCommGrpCat.{w}
  let : HasExt.{w} (Sheaf J AddCommGrpCat.{w}) := hasExt_of_enoughInjectives _
  intro q
  let : Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf R).obj I) (q + 1) U) :=
    injective_module_abelian_acyclic U I (q + 1) (Nat.succ_pos q)
  obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived J U (q + 1)
  have hz : IsZero (Sheaf.H' ((SheafOfModules.toSheaf R).obj I) (q + 1) U) :=
    AddCommGrpCat.isZero_of_subsingleton _
  exact hz.of_iso (e.app _).symm

private theorem small_module_evaluation_acyclic.{w}
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{w}) [EnoughInjectives (SheafOfModules.{w} R)]
    (U : C) (M : SheafOfModules.{w} R)
    (hM : (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)).rightAcyclic
        ((SheafOfModules.toSheaf R).obj M)) :
    (SheafOfModules.evaluation.{w} R (op U)).rightAcyclic M := by
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{w} J AddCommGrpCat.{w}
  let F := SheafOfModules.toSheaf R
  let B := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)
  let E := SheafOfModules.evaluation.{w} R (op U)
  have : E.Additive := Functor.additive_of_preserves_binary_products _
  let V := forget₂ (ModuleCat.{w} (R.obj.obj (op U))) AddCommGrpCat.{w}
  intro q
  let e := Functor.compRightDerivedObjIso F B
    (fun I _ ↦ small_forgotten_injective_acyclic J R U I) (q + 1) M
  have hz : IsZero (((E ⋙ V).rightDerived (q + 1)).obj M) := (hM q).of_iso e
  have hz' : IsZero (V.obj ((E.rightDerived (q + 1)).obj M)) :=
    hz.of_iso (Functor.rightDerivedCompObjIso E V (q + 1) M).symm
  apply (IsZero.iff_id_eq_zero _).2
  apply V.map_injective
  exact hz'.eq_of_src _ _

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
