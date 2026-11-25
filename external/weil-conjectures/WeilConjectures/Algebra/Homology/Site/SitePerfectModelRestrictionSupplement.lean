/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Homology.SitePerfectModelRestriction

/-! # Exact restriction and transport of strict-perfect packages

Source: Stacks Project, Modules on Sites, Tags 03DJ and 04IX.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' r m w w'
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

private theorem pushforward_finiteLimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [G.IsContinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    PreservesFiniteLimits (pushforward.{m} φ) := by
  let T := forget.{m} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (pushforward.{m} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((forget.{m} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem pushforward_finiteColimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {G : C ⥤ D} [G.IsContinuous J K] [G.IsCocontinuous J K]
    [∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{m}), G.op.HasPointwiseRightKanExtension F]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    PreservesFiniteColimits (pushforward.{m} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{m} J K
  have : PreservesColimitsOfSize.{0, 0} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{m} J K).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (toSheaf.{m} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  let T := toSheaf.{m} S
  have : PreservesFiniteColimits (pushforward.{m} φ ⋙ T) := by
    change PreservesFiniteColimits (toSheaf.{m} R ⋙ H)
    infer_instance
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- Further slice restriction is exact, at independent universes.
Source: Stacks Project, Tag 04IX. Restriction commutes with kernels and sheafified
cokernels through the same abelian-sheaf comparison.
(blueprint: lem-sf-site-perfect-overmap-exact). -/
theorem overMap_exact_ofUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {U V : C} (f : V ⟶ U)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [HasSheafify (J.over V) AddCommGrpCat.{max u v r}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r}] :
    PreservesFiniteLimits (overMap.{max u v r} R f) ∧
      PreservesFiniteColimits (overMap.{max u v r} R f) := by
  exact ⟨pushforward_finiteLimits (Sheaf.pushforwardOverMapIso _ f).inv,
    pushforward_finiteColimits.{max u v, v, max u v, v, r, max u v r}
      (Sheaf.pushforwardOverMapIso _ f).inv⟩

/-- Successive slice restrictions compose. Source: Stacks Project, Tag 04IX.
The comparison is induced by associativity of arrows in the slice.
(blueprint: lem-sf-site-perfect-overmap-comp). -/
def sitePerfectOverMapComp
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    overMap.{max u v r} R f ⋙ overMap R g ≅ overMap R (g ≫ f) := by
  have : (Over.map g ⋙ Over.map f).IsContinuous (J.over W) (J.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over V) _
  let e := pushforwardComp (Sheaf.pushforwardOverMapIso R g).inv
    (Sheaf.pushforwardOverMapIso R f).inv
  refine e ≪≫ pushforwardNatIso _ (Over.mapComp g f) ≪≫ pushforwardCongr ?_
  ext Z : 3
  simp [Sheaf.pushforwardOverMapIso]
  rfl

/-- The chosen representative definition of derived restriction agrees with the
functor induced by exact module restriction. Source: Stacks Project, Tag 03DJ.
The comparison first uses the localization comparison on the chosen representative,
then applies the derived functor to the representative's canonical isomorphism.
(blueprint: lem-sf-site-perfect-derived-restriction-iso). -/
def overFunctor_derivedRestrictionIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max u v r} R)]
    [HasDerivedCategory.{w'} (SheafOfModules.{max u v r} (R.over U))]
    (E : DerivedCategory (SheafOfModules.{max u v r} R)) :
    let _ : PreservesFiniteLimits (overFunctor.{max u v r} R U) :=
      (overFunctor_exact_ofUniverses R U).1
    let _ : PreservesFiniteColimits (overFunctor.{max u v r} R U) :=
      (overFunctor_exact_ofUniverses R U).2
    ringedSiteDerivedRestrictionOfUniverses R U E ≅
      (overFunctor.{max u v r} R U).mapDerivedCategory.obj E := by
  let F := overFunctor.{max u v r} R U
  have : PreservesFiniteLimits F := (overFunctor_exact_ofUniverses R U).1
  have : PreservesFiniteColimits F := (overFunctor_exact_ofUniverses R U).2
  exact (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage E)).symm ≪≫
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E)

/-- An additive finite-limit-preserving functor that preserves the rank-one free module
transports every displayed finite-free splitting. Source: Stacks Project, Tag 04IX.
The comparison is the product comparison followed by the given rank-one isomorphisms.
(blueprint: lem-sf-site-perfect-package-map). -/
def StrictPerfectCoefficientPackageOnSite.map
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    (F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S)
    [F.Additive] [PreservesFiniteLimits F]
    (e : F.obj (unit R) ≅ unit S)
    {P : CochainComplex (SheafOfModules.{r} R) ℤ}
    (p : StrictPerfectCoefficientPackageOnSite R P) :
    StrictPerfectCoefficientPackageOnSite S ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  let e' (n : ℤ) := PreservesProduct.iso F (fun _ : Fin (p.N n) ↦ unit R) ≪≫
    Pi.mapIso (fun _ : Fin (p.N n) ↦ e)
  exact
    { N := p.N
      i n := F.map (p.i n) ≫ (e' n).hom
      p n := (e' n).inv ≫ F.map (p.p n)
      splitting n := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, p.splitting, F.map_id]
        rfl }

end SheafOfModules
