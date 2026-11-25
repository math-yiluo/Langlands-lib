/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact

/-!
# Exact restriction and extension by zero on a localized ringed site

Source: Stacks Project, Modules on Sites, Section 03DH and Lemmas 03DI, 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

private theorem overFunctor_shortExact
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (U : C)
    [(overFunctor.{u} R U).PreservesZeroMorphisms]
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact) :
    (S.map (overFunctor.{u} R U)).ShortExact := by
  have : PreservesFiniteColimits (toSheaf.{u} R) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful R).2.2.1
  have : (overFunctor.{u} R U).Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  let e : overFunctor.{u} R U ⋙ toSheaf (R.over U) ≅
      toSheaf R ⋙ J.toGrothendieck.overPullback AddCommGrpCat.{u} U := Iso.refl _
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (toSheaf (R.over U))
  exact ShortComplex.shortExact_of_iso (S.mapNatIso e.symm)
    (CategoryTheory.siteRestriction_exact J U (S.map (toSheaf R))
      (hS.map_of_exact (toSheaf R)))

open Classical in
private theorem extensionRestrict_of
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
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
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) (G : SheafOfModules.{u} R)
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
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) (G : SheafOfModules.{u} R)
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
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) (G : SheafOfModules.{u} R) :
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
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) (G H : SheafOfModules.{u} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) (b : G ⟶ H) :
    extensionPresheafHomEquiv R U F H (a ≫ b.val) =
      extensionPresheafHomEquiv R U F G a ≫ (overFunctor R U).map b := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem extensionPresheafHomEquiv_naturality_left_symm
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F H : SheafOfModules.{u} (R.over U)) (G : SheafOfModules.{u} R)
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
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) :
    (extensionByZeroPresheaf.{u} R U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 R.obj)) ⊣ overFunctor.{u} R U := by
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
    have heq (P : PresheafOfModules.{u} R.obj) (G : SheafOfModules.{u} R) :
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

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the localized ringed site is exact. The sheafification of the
extension-by-zero presheaf is exact and left adjoint to restriction. The adjunction
contains the Hom equivalence, natural in both module sheaves.

Source: Stacks Project, Modules on Sites, Section 03DH and Lemmas 03DI, 03DJ
(blueprint: lem-pur-site-restriction-module-adjunction-exact).

Proof:
1. Restriction keeps the section modules and their restriction maps, by
   `def-pur-localized-ringed-site`. Compose `def-weil-extension-by-zero-presheaf`
   with `def-weil-presheaf-modules-sheafification` to obtain the extension functor.
2. By `lem-pc-sites-module-sheafification-interface`, its underlying abelian sheaf
   is the sheafified direct-sum extension. Apply the natural Hom bijection of
   `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`. Its sectionwise formula
   respects multiplication by sections of the ring sheaf in both directions,
   so it restricts to the natural bijection of module Hom sets.
3. Forget a short exact sequence to abelian sheaves using
   `situation-conventions`. Apply
   `lem-weil-pbc-site-restriction-exact` and reflect exactness through the faithful
   exact forgetful functor. This proves exactness of module restriction.
4. The underlying abelian extension is isomorphic to the left adjoint of
   `lem-weil-pbc-site-restriction-adjunction`, by uniqueness of left adjoints and
   `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`. Its exactness follows
   from `lem-weil-pbc-site-extension-by-zero-exact`. Reflect exactness through
   the module forgetful functor, using the sheafification interface again. -/
theorem localizedModule_adjunction_exact
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (O : Sheaf J.toGrothendieck CommRingCat.{u}) (U : C) :
    PreservesFiniteLimits
        (overFunctor.{u} ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U) ∧
      PreservesFiniteColimits
        (overFunctor.{u} ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U) ∧
      PreservesFiniteLimits
        (extensionByZeroPresheaf.{u}
            ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O).obj)) ∧
      PreservesFiniteColimits
        (extensionByZeroPresheaf.{u}
            ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O).obj)) ∧
      Nonempty (Adjunction
        (extensionByZeroPresheaf.{u}
            ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O).obj))
        (overFunctor.{u}
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O) U)) := by
  let R := ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj O)
  have : PreservesFiniteColimits (toSheaf.{u} R) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful R).2.2.1
  have : PreservesFiniteColimits (toSheaf.{u} (R.over U)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful (R.over U)).2.2.1
  let T := overFunctor.{u} R U
  have : T.Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  let L := extensionByZeroPresheaf.{u} R U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let A := Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget U) AddCommGrpCat.{u} (J.toGrothendieck.over U) J.toGrothendieck
  obtain ⟨adj, _⟩ := CategoryTheory.siteExtensionByZeroPresheaf_adjunction J U
  let e := Adjunction.leftAdjointUniq adj
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.forget U) AddCommGrpCat.{u} (J.toGrothendieck.over U) J.toGrothendieck)
  obtain ⟨hA, hExact⟩ := CategoryTheory.site_extensionByZero_exact J U
  let := hA
  have eP : extensionByZeroPresheaf.{u} R U ⋙ PresheafOfModules.toPresheaf R.obj ≅
      toSheaf (R.over U) ⋙ sheafToPresheaf (J.toGrothendieck.over U) AddCommGrpCat.{u} ⋙
        siteExtensionByZeroPresheaf U := by
    classical
    refine NatIso.ofComponents (fun F ↦ Iso.refl _) ?_
    intro F G f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    ext V x
    change (DirectSum.lmap (R := R.obj.obj V) (fun φ : V.unop ⟶ U ↦
      (f.val.app (Opposite.op (Over.mk φ))).hom)) x =
        (DirectSum.toAddMonoid (fun φ : V.unop ⟶ U ↦
          (DirectSum.of _ φ).comp
            (f.val.app (Opposite.op (Over.mk φ))).hom.toAddMonoidHom)) x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of φ x =>
      simp only [DirectSum.lmap_of, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  let eL : L ⋙ toSheaf R ≅ toSheaf (R.over U) ⋙ siteExtensionByZeroSheaf J U :=
    (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight eP (presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}) ≪≫
            Functor.associator _ _ _
  have hLA : (L ⋙ toSheaf R).Additive := by
    have : PreservesColimitsOfSize.{u, u} A :=
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Over.forget U) AddCommGrpCat.{u} (J.toGrothendieck.over U)
        J.toGrothendieck).leftAdjoint_preservesColimits
    have : PreservesBinaryBiproducts A :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts A
    have : A.Additive := A.additive_of_preservesBinaryBiproducts
    have : (siteExtensionByZeroSheaf J U).Additive :=
      Functor.additive_of_iso e.symm
    exact Functor.additive_of_iso eL.symm
  have hL : L.Additive := Functor.additive_of_comp_faithful L (toSheaf R)
  have hLexact : ∀ S : ShortComplex (SheafOfModules.{u} (R.over U)),
      S.ShortExact → (S.map L).ShortExact := by
    intro S hS
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (toSheaf R)
    have h := hExact (S.map (toSheaf (R.over U)))
      (hS.map_of_exact (toSheaf (R.over U)))
    let e' := eL ≪≫ Functor.isoWhiskerLeft (toSheaf (R.over U)) e
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e'.symm) h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (T.preservesFiniteLimits_iff_forall_exact_map_and_mono).mpr
      (fun S hS ↦ ⟨(overFunctor_shortExact J R U S hS).exact,
        (overFunctor_shortExact J R U S hS).mono_f⟩)
  · exact (T.preservesFiniteColimits_iff_forall_exact_map_and_epi).mpr
      (fun S hS ↦ ⟨(overFunctor_shortExact J R U S hS).exact,
        (overFunctor_shortExact J R U S hS).epi_g⟩)
  · exact (L.preservesFiniteLimits_iff_forall_exact_map_and_mono).mpr
      (fun S hS ↦ ⟨(hLexact S hS).exact, (hLexact S hS).mono_f⟩)
  · exact (L.preservesFiniteColimits_iff_forall_exact_map_and_epi).mpr
      (fun S hS ↦ ⟨(hLexact S hS).exact, (hLexact S hS).epi_g⟩)
  · exact ⟨extensionSheafAdjunction R U⟩

end SheafOfModules
