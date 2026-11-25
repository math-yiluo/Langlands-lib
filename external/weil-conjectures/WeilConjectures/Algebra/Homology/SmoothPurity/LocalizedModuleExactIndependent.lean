/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exact localized module adjunction with independent site universes

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1}) (U : C)

/-- The existing direct-sum extension presheaf followed by module sheafification.
Source: Stacks 03DI (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
abbrev localizedModuleExtension :=
  extensionByZeroPresheaf.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ⋙
      PresheafOfModules.sheafification (𝟙 _)

/-- The existing sectionwise restriction to the slice ring.
Source: Stacks 03DJ (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
def localizedModuleRestriction :=
  overFunctor.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U

open Classical in
private theorem extensionRestrict_of
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U F a
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk χ))) ψ
        (F.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionPresheafToHom
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) :
    F ⟶ (overFunctor R U).obj G where
  val.app X := ModuleCat.ofHom
    ((a.app (Opposite.op X.unop.left)).hom.comp
      (DirectSum.lof (R.obj.obj (Opposite.op X.unop.left)) (X.unop.left ⟶ U)
        (fun φ ↦ F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom))
  val.naturality {X Y} f := by
    ext x
    have h := PresheafOfModules.naturality_apply a
      ((Over.forget U).op.map f)
      (DirectSum.of _ X.unop.hom x)
    change a.app (Opposite.op Y.unop.left)
        (extensionByZeroPresheafRestrictAdd R U F ((Over.forget U).op.map f)
          (DirectSum.of _ X.unop.hom x)) = _ at h
    have hr := extensionRestrict_of R U F ((Over.forget U).op.map f)
      X.unop.hom Y.unop.hom (Over.w f.unop) x
    erw [hr] at h
    have hf : (Over.homMk f.unop.left (Over.w f.unop) : Y.unop ⟶ X.unop) =
        f.unop := by ext; rfl
    erw [hf] at h
    change a.app (Opposite.op Y.unop.left)
        (DirectSum.of (fun φ : Y.unop.left ⟶ U ↦
          F.val.obj (Opposite.op (Over.mk φ))) Y.unop.hom (F.val.map f x)) =
      G.val.map ((Over.forget U).op.map f)
        (a.app (Opposite.op X.unop.left)
          (DirectSum.of (fun φ : X.unop.left ⟶ U ↦
            F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom x))
    exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionHomToPresheaf
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R)
    (a : F ⟶ (overFunctor R U).obj G) :
    extensionByZeroPresheafObj R U F ⟶ G.val where
  app V := ModuleCat.ofHom (DirectSum.toModule _ _ _
    (fun φ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
  naturality {V W} f := by
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of φ x =>
      change (DirectSum.toModule (R.obj.obj W) _ (G.val.obj W)
        (fun ψ : W.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
        (extensionByZeroPresheafRestrictAdd R U F f
          (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x)) =
          G.val.map f ((DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
            (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x))
      erw [extensionRestrict_of R U F f φ (f.unop ≫ φ) rfl]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply a.val
        (Opposite.op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionPresheafHomEquiv
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R) :
    (extensionByZeroPresheafObj R U F ⟶ G.val) ≃
      (F ⟶ (overFunctor R U).obj G) where
  toFun := extensionPresheafToHom R U F G
  invFun := extensionHomToPresheaf R U F G
  left_inv a := by
    ext V x
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun φ : V.unop ⟶ U ↦ (a.app V).hom.comp
        (DirectSum.lof (R.obj.obj V) _ _ φ))) x = (a.app V) x
    exact (DirectSum.toModule.unique _ (a.app V).hom x).symm
  right_inv a := by
    ext X x
    change (DirectSum.toModule (R.obj.obj (Opposite.op X.unop.left)) _
      (G.val.obj (Opposite.op X.unop.left))
      (fun φ : X.unop.left ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
        (DirectSum.lof _ _ _ X.unop.hom x) = (a.val.app X) x
    erw [DirectSum.toModule_lof]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPresheafHomEquiv_naturality_right
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G H : SheafOfModules.{u + 1} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) (b : G ⟶ H) :
    extensionPresheafHomEquiv R U F H (a ≫ b.val) =
      extensionPresheafHomEquiv R U F G a ≫ (overFunctor R U).map b := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem extensionPresheafHomEquiv_naturality_left_symm
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F H : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R)
    (a : H ⟶ F) (b : F ⟶ (overFunctor R U).obj G) :
    (extensionPresheafHomEquiv R U H G).symm (a ≫ b) =
      (extensionByZeroPresheaf R U).map a ≫
        (extensionPresheafHomEquiv R U F G).symm b := by
  ext V x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of φ x =>
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun ψ : V.unop ⟶ U ↦ ((a ≫ b).val.app (Opposite.op (Over.mk ψ))).hom))
        (DirectSum.of _ φ x) =
      (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
        (fun ψ : V.unop ⟶ U ↦ (b.val.app (Opposite.op (Over.mk ψ))).hom))
          (DirectSum.lmap (R := R.obj.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom)
              (DirectSum.of _ φ x))
    erw [DirectSum.lmap_of, DirectSum.toModule_lof, DirectSum.toModule_lof]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extensionSheafAdjunction
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J RingCat.{u + 1}) (U : C) :
    (extensionByZeroPresheaf.{u + 1} R U ⋙
      PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)) ⊣ overFunctor.{u + 1} R U := by
  refine Adjunction.mkOfHomEquiv ?_
  refine
    { homEquiv := fun F G ↦
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
          (extensionPresheafHomEquiv R U F G)
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro H F G a b
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        ((extensionPresheafHomEquiv R U H G).symm (a ≫ b)) = _
    rw [extensionPresheafHomEquiv_naturality_left_symm]
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left_symm
      ((extensionByZeroPresheaf R U).map a)
      ((extensionPresheafHomEquiv R U F G).symm b)
    have heq (P : PresheafOfModules.{u + 1} R.obj) (G : SheafOfModules.{u + 1} R) :
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P G =
          PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [heq, heq] at h
    exact h
  · intro F G H a b
    change extensionPresheafHomEquiv R U F H
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b)) = _
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right
      a b
    change PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) a ≫ b.val at h
    erw [h]
    exact extensionPresheafHomEquiv_naturality_right R U F G H _ b

/-- Both localized module functors are additive and exact at the original site universes.
Source: Stacks 03DI and 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
Proof:
1. By def-pur-localized-ringed-site, restriction keeps section modules, scalar actions,
   and restriction maps. Compose def-weil-extension-by-zero-presheaf with
   def-weil-presheaf-modules-sheafification to obtain the extension functor.
2. Construct the module Hom equivalence by composing with each direct-sum injection;
   its inverse uses DirectSum.toModule on the component linear maps. Check naturality
   and the inverse laws on summand generators. Compose with the sheafification Hom
   equivalence of lem-pc-sites-module-sheafification-interface to obtain the adjunction.
3. Forget a short exact complex to abelian sheaves using
   situation-conventions. Restriction commutes with forgetting
   sectionwise, so lem-weil-pbc-site-restriction-exact applies. Reflect short exactness
   through the faithful exact module forgetful functor. Restriction is additive
   sectionwise; the abelian exactness criteria give both finite preservation clauses.
4. Direct-sum induction identifies extension followed by forgetting with the abelian
   extension presheaf. Use lem-pc-sites-module-sheafification-interface to sheafify this
   comparison. By lem-weil-pbc-site-extension-by-zero-presheaf-adjoint and uniqueness
   of left adjoints, the abelian extension is the constructed sheaf pullback. Transfer
   its additivity through the comparison and the faithful module forgetful functor.
   Apply lem-weil-pbc-site-extension-by-zero-exact, transport the short exact complex
   along the comparison, and reflect short exactness. The same abelian criteria give
   the extension's finite-limit and finite-colimit preservation. These comparisons
   retain the original site and coefficient universes throughout. -/
theorem localizedModuleExactIndependent :
    (localizedModuleExtension R U).Additive ∧
      PreservesFiniteLimits (localizedModuleExtension R U) ∧
      PreservesFiniteColimits (localizedModuleExtension R U) ∧
      (localizedModuleRestriction R U).Additive ∧
      PreservesFiniteLimits (localizedModuleRestriction R U) ∧
      PreservesFiniteColimits (localizedModuleRestriction R U) := by
  let S := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let L := localizedModuleExtension R U
  let T := localizedModuleRestriction R U
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1,
      u + 1, u + 1} _
  have : HasSheafify (J.over U) AddCommGrpCat.{u + 1} :=
    instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
      u + 1, u + 2, u, u + 1, u + 1} _ _
  have : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  let adj : L ⊣ T := extensionSheafAdjunction S U
  have : PreservesColimitsOfSize.{0, 0} L :=
    adj.leftAdjoint_preservesColimits
  have : T.Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  have : L.Additive := adj.left_adjoint_additive
  have : (extensionByZeroPresheaf.{u + 1} S U).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    apply PresheafOfModules.mono_of_injective
    intro V
    change Function.Injective (DirectSum.lmap (R := S.obj.obj V)
      (fun φ : V.unop ⟶ U ↦ (f.val.app (op (Over.mk φ))).hom))
    apply (DirectSum.lmap_injective _).mpr
    intro φ
    apply (ModuleCat.mono_iff_injective _).mp
    exact inferInstanceAs (Mono ((evaluation.{u + 1} (S.over U) (op (Over.mk φ))).map f))
  have : L.PreservesMonomorphisms :=
    inferInstanceAs ((extensionByZeroPresheaf.{u + 1} S U ⋙
      PresheafOfModules.sheafification.{u + 1} (𝟙 S.obj)).PreservesMonomorphisms)
  have : L.PreservesHomology := L.preservesHomology_of_preservesMonos_and_cokernels
  have : PreservesFiniteLimits L := L.preservesFiniteLimits_of_preservesHomology
  have : PreservesLimitsOfSize.{0, 0} T := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{0, 0}
      (J.overPullback AddCommGrpCat.{u + 1} U) :=
    ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (J.over U) J).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (toSheaf.{u + 1} S) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful S).2.2.1
  have : PreservesFiniteColimits (T ⋙ toSheaf.{u + 1} (S.over U)) :=
    inferInstanceAs (PreservesFiniteColimits
      (toSheaf.{u + 1} S ⋙ J.overPullback AddCommGrpCat.{u + 1} U))
  have : PreservesFiniteColimits (toSheaf.{u + 1} (S.over U)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful (S.over U)).2.2.1
  have : ReflectsFiniteColimits (toSheaf.{u + 1} (S.over U)) :=
    inferInstance
  have : PreservesFiniteColimits T :=
    preservesFiniteColimits_of_reflects_of_preserves T (toSheaf.{u + 1} (S.over U))
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- Additivity of extension. Source: Stacks 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleExtension_additive : (localizedModuleExtension R U).Additive :=
  (localizedModuleExactIndependent R U).1

/-- Left exactness of extension. Source: Stacks 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleExtension_limits :
    PreservesFiniteLimits (localizedModuleExtension R U) :=
  (localizedModuleExactIndependent R U).2.1

/-- Right exactness of extension. Source: Stacks 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleExtension_colimits :
    PreservesFiniteColimits (localizedModuleExtension R U) :=
  (localizedModuleExactIndependent R U).2.2.1

/-- Additivity of restriction. Source: Stacks 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleRestriction_additive : (localizedModuleRestriction R U).Additive :=
  (localizedModuleExactIndependent R U).2.2.2.1

/-- Left exactness of restriction. Source: Stacks 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleRestriction_limits :
    PreservesFiniteLimits (localizedModuleRestriction R U) :=
  (localizedModuleExactIndependent R U).2.2.2.2.1

/-- Right exactness of restriction. Source: Stacks 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
instance localizedModuleRestriction_colimits :
    PreservesFiniteColimits (localizedModuleRestriction R U) :=
  (localizedModuleExactIndependent R U).2.2.2.2.2

open Classical in
/-- The canonical adjunction is fixed by insertion into the summand indexed by the
structure arrow, followed by the sheafification unit.
Source: Stacks 03DI (blueprint: lem-pur-site-restriction-module-adjunction-exact).
Proof: a map from the direct sum is a family of maps from its summands. Naturality
identifies this family with a map on the slice. Sheafification extends this bijection
to sheaves. Its unit is the displayed insertion, which determines the adjunction
uniquely since the summands generate the extension presheaf locally. -/
theorem localizedModuleAdjunctionIndependent_existsUnique :
    ∃! adj : localizedModuleExtension R U ⊣ localizedModuleRestriction R U,
      ∀ (M : Mod (R.over U)) (W : (Over U)ᵒᵖ) (m : M.val.obj W),
        (adj.unit.app M).val.app W m =
          ((PresheafOfModules.sheafificationAdjunction.{u + 1}
            (𝟙 ((sheafCompose J
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
            ((extensionByZeroPresheaf.{u + 1}
              ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U).obj M)).app
                (op W.unop.left)
                  (DirectSum.lof (R.obj.obj (op W.unop.left)) (W.unop.left ⟶ U)
                    (fun a ↦ M.val.obj (op (Over.mk a))) W.unop.hom m) := by
  let S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let adj := extensionSheafAdjunction S U
  refine ⟨adj, ?_, ?_⟩
  · intro M W m
    rfl
  · intro adj' h'
    apply Adjunction.ext
    ext M W m
    exact h' M W m

/-- The uniquely normalized localized module adjunction.
Source: Stacks 03DI (blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
def localizedModuleAdjunctionIndependent :
    localizedModuleExtension R U ⊣ localizedModuleRestriction R U :=
  Classical.choose (localizedModuleAdjunctionIndependent_existsUnique R U).exists

/-- Its termwise derived adjunction, obtained by localization at quasi-isomorphisms.
Source: Stacks 015F and 03DI
(blueprint: lem-pur-site-restriction-module-adjunction-exact). -/
def localizedModuleDerivedAdjunction :
    (localizedModuleExtension R U).mapDerivedCategory ⊣
      (localizedModuleRestriction R U).mapDerivedCategory :=
  letI : CatCommSq ((localizedModuleExtension R U).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
        (localizedModuleExtension R U).mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq ((localizedModuleRestriction R U).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q
        (localizedModuleRestriction R U).mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  ((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (localizedModuleExtension R U).mapDerivedCategory
    (localizedModuleRestriction R U).mapDerivedCategory

end SheafOfModules
