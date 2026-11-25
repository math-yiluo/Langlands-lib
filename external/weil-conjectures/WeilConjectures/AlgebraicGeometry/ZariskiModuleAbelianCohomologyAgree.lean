/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Cohomology of a Zariski module and its underlying abelian sheaf

Source: Stacks Project, `sites-cohomology.tex`, Lemma Tag 03FD
(blueprint: lem-sc-zariski-module-abelian-cohomology-agree).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace AlgebraicGeometry

private noncomputable def zeroEquiv {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (F : Sheaf J AddCommGrpCat.{u}) (U : C) :
    (Sheaf.H' F 0 U : Type u) ≃+ F.obj.obj (op U) where
  toEquiv := Abelian.Ext.addEquiv₀.toEquiv |>.trans
    ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ F) |>.trans
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj) |>.trans
    yonedaEquiv
  map_add' x y := by
    change ((toSheafify J _ ≫ (Abelian.Ext.addEquiv₀ (x + y)).hom).app (op U))
      (FreeAbelianGroup.of (𝟙 U)) =
      ((toSheafify J _ ≫ (Abelian.Ext.addEquiv₀ x).hom).app (op U))
        (FreeAbelianGroup.of (𝟙 U)) +
      ((toSheafify J _ ≫ (Abelian.Ext.addEquiv₀ y).hom).app (op U))
        (FreeAbelianGroup.of (𝟙 U))
    rw [map_add]
    rfl

private theorem zeroEquiv_apply {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (F : Sheaf J AddCommGrpCat.{u}) (U : C)
    (x : Sheaf.H' F 0 U) :
    zeroEquiv F U x = ((toSheafify J _ ≫ (Abelian.Ext.addEquiv₀ x).hom).app (op U))
      (FreeAbelianGroup.of (𝟙 U)) := rfl

private theorem zeroEquiv_naturality {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    {F G : Sheaf J AddCommGrpCat.{u}} (U : C)
    (f : F ⟶ G) (x : Sheaf.H' F 0 U) :
    zeroEquiv G U (((Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      f.hom.app (op U) (zeroEquiv F U x) := by
  have h : Abelian.Ext.addEquiv₀
      (((Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      Abelian.Ext.addEquiv₀ x ≫ f := by
    apply Abelian.Ext.addEquiv₀.symm.injective
    change Abelian.Ext.mk₀ _ = Abelian.Ext.mk₀ _
    rw [Abelian.Ext.mk₀_addEquiv₀_apply, ← Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.mk₀_addEquiv₀_apply]
    rfl
  rw [zeroEquiv_apply, h, zeroEquiv_apply]
  rfl

private noncomputable def zeroIso {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] :
    Sheaf.cohomologyPresheafFunctor J 0 ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) :=
  NatIso.ofComponents (fun F ↦ (zeroEquiv F U).toAddCommGrpIso)
    (fun f ↦ by
      ext x
      exact zeroEquiv_naturality U f x)


/-- For a scheme and an `𝒪_X`-module, module cohomology agrees canonically and naturally
with cohomology of the underlying abelian sheaf on the small Zariski site.

Source: Stacks Project, `sites-cohomology.tex`, Lemma Tag 03FD
(blueprint: lem-sc-zariski-module-abelian-cohomology-agree).

Proof: apply `lem-sc-module-abelian-zariski-cohomology` to obtain the comparison in every
positive degree. In degree zero, both right derived functors are global sections by
`pqf-def-cohomology` and `lemma-uniform-bounds-pro-etale-affines`; choose the identity on sections.
The comparison is natural in the module by the naturality in the cited comparison and by
functoriality of global sections in degree zero.

The last equality spells out the degree-zero identity: send a section through the
canonical map `Γ → R⁰Γ`, then through `e 0`; identify `Ext⁰` with morphisms from the
sheafified free abelian representable, precompose with the sheafification unit, and
evaluate at the generator given by the identity of the top open. The resulting section
must be the original section. Enough injectives for abelian sheaves is supplied by the
Grothendieck structure of sheaves on the small Zariski site, rather than assumed. -/
theorem zariskiModuleAbelianCohomologyAgree (X : Scheme.{u}) :
    ∃ e : ∀ q : ℕ,
      (RingedSpace.moduleCohomology X.toRingedSpace q ⋙
        forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{u}) ≅
      (SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
        @CategoryTheory.Sheaf.cohomologyPresheafFunctor.{u, u, u}
          (Opens X.carrier) inferInstance (Opens.grothendieckTopology X.carrier)
          inferInstance
          (@hasExt_of_enoughInjectives _ _ _ inferInstance
            (@IsGrothendieckAbelian.enoughInjectives _ _ _
              (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
                (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) q ⋙
        (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)),
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (s : (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M),
        ((toSheafify (Opens.grothendieckTopology X.carrier)
              (yoneda.obj (⊤ : Opens X.carrier) ⋙ AddCommGrpCat.free) ≫
            (@Abelian.Ext.addEquiv₀ _ _ _
              (@hasExt_of_enoughInjectives _ _ _ inferInstance
                (@IsGrothendieckAbelian.enoughInjectives _ _ _
                  (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
                    (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) _ _
              ((e 0).hom.app M
                ((forget₂
                    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
                    AddCommGrpCat.{u}).map
                  ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app M)
                  s))).hom).app (op ⊤))
          (FreeAbelianGroup.of (𝟙 (⊤ : Opens X.carrier))) = s := by
  classical
  let : EnoughInjectives
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
        (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let : PreservesFiniteLimits G :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  let a := Functor.isoWhiskerRight G.rightDerivedZeroIsoSelf V
  let b := Functor.isoWhiskerLeft T
    (zeroIso (Opens.grothendieckTopology X.carrier) (⊤ : Opens X.carrier))
  let c : G ⋙ V ≅ T ⋙ sheafToPresheaf
      (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
    Iso.refl _
  let e₀ := a ≪≫ c ≪≫ b.symm
  refine ⟨fun q ↦ Nat.casesOn q e₀ (fun n ↦
    (zariskiModuleAbelianCohomologyNatural X (n + 1)).some), ?_⟩
  intro M s
  change zeroEquiv (T.obj M) (⊤ : Opens X.carrier)
    (e₀.hom.app M (V.map (G.toRightDerivedZero.app M) s)) = s
  change zeroEquiv (T.obj M) (⊤ : Opens X.carrier)
    ((zeroEquiv (T.obj M) (⊤ : Opens X.carrier)).symm
      (V.map (G.rightDerivedZeroIsoSelf.hom.app M)
        (V.map (G.toRightDerivedZero.app M) s))) = s
  rw [AddEquiv.apply_symm_apply]
  change (V.map (G.toRightDerivedZero.app M) ≫
    V.map (G.rightDerivedZeroIsoSelf.hom.app M)) s = s
  rw [← V.map_comp, G.rightDerivedZeroIsoSelf_inv_hom_id_app, V.map_id]
  rfl

end AlgebraicGeometry
