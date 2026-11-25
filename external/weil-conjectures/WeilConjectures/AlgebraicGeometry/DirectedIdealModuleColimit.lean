/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-!
# Directed unions of ideal module sheaves
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A nonempty directed union of ideal sheaves is a colimit of their module sheaves.

Source: Stacks Project, Properties, Tag 01PG (the union argument for submodules),
applied to ideal sheaves.
(blueprint: lem-pqf-directed-ideal-module-colimit).

Proof: Transport each stage along e to its ideal module. The displayed compatibility
identifies each cocone leg with the inclusion into I and, by monicity of the inclusion
of I into the structure sheaf, identifies every transition with the ideal inclusion.
On an affine open U, the equality sSup S = I identifies I.ideal U with the supremum
of the stage ideals. Since S is nonempty and directed, any element of this supremum
belongs to one stage. Given any other cocone, define its descent on an affine section
by choosing a stage containing the section and applying its cocone leg. Directedness
provides a common upper stage, so the result is independent of the choice. The same
argument proves addition and scalar multiplication. Restriction to a smaller affine
open preserves membership in the chosen stage and commutes with its cocone map, so
these linear maps commute with restriction. The affine opens form a basis, hence the
maps extend uniquely to a morphism of sheaves of modules. Its composites with the
stage inclusions are the given legs, as can be checked on this basis. Conversely any
such morphism has these values on every affine section, so it is unique. This is the
colimit universal property. On the empty scheme the same basis argument is vacuous;
nonemptiness of S also ensures that zero sections have a stage. -/
theorem nonempty_isColimit_of_directed_ideal_modules {X : Scheme.{u}}
    (I : X.IdealSheafData) (S : Set X.IdealSheafData)
    (hne : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) (hunion : sSup S = I)
    (D : S ⥤ X.Modules) (τ : D ⟶ (Functor.const S).obj I.toModules)
    (e : ∀ a : S, D.obj a ≅ a.val.toModules)
    (he : ∀ a : S, (e a).inv ≫ τ.app a ≫ I.toModulesι = a.val.toModulesι) :
    Nonempty (IsColimit (Cocone.mk I.toModules τ)) := by
  classical
  have hc (a : S) : τ.app a ≫ I.toModulesι = (e a).hom ≫ a.val.toModulesι := by
    rw [← he a]
    simp
  have hinj (a : S) (U : X.Opens) : Function.Injective ((τ.app a).app U) := by
    intro x y hxy
    have hh : (e a).hom.app U x = (e a).hom.app U y := by
      apply a.val.injective_toModulesι_app U
      have hx := congr($(hc a).app U x)
      have hy := congr($(hc a).app U y)
      exact hx.symm.trans ((congrArg (I.toModulesι.app U) hxy).trans hy)
    have hback := congrArg ((e a).inv.app U) hh
    simpa only [← ConcreteCategory.comp_apply, ← Modules.Hom.comp_app,
      Iso.hom_inv_id, Modules.Hom.id_app, CategoryTheory.id_apply] using hback
  have hex (U : X.affineOpens) (x : Γ(I.toModules, U.1)) :
      ∃ a : S, ∃ y : Γ(D.obj a, U.1), (τ.app a).app U.1 y = x := by
    have hx : I.toModulesι.app U.1 x ∈ I.ideal U :=
      (I.range_toModulesι_app U).subset ⟨x, rfl⟩
    have hsup : I.ideal U = ⨆ a : S, a.val.ideal U := by
      rw [← hunion, sSup_eq_iSup', ideal_iSup, iSup_apply]
    have : Nonempty S := hne.to_subtype
    have hdir' : Directed (· ≤ ·) (fun a : S ↦ a.val.ideal U) := by
      intro a b
      obtain ⟨c, hcS, hac, hbc⟩ := hdir a.val a.property b.val b.property
      exact ⟨⟨c, hcS⟩, hac U, hbc U⟩
    rw [hsup] at hx
    obtain ⟨a, ha⟩ := (Submodule.mem_iSup_of_directed _ hdir').mp hx
    obtain ⟨y, hy⟩ := (a.val.range_toModulesι_app U).superset ha
    refine ⟨a, (e a).inv.app U.1 y, I.injective_toModulesι_app U.1 ?_⟩
    exact congr($(he a).app U.1 y) |>.trans hy
  have hab (a b : S) : ∃ c : S, a ≤ c ∧ b ≤ c := by
    obtain ⟨c, hcS, hac, hbc⟩ := hdir a.val a.property b.val b.property
    exact ⟨⟨c, hcS⟩, hac, hbc⟩
  choose a y hy using hex
  have hτ {a b : S} (f : a ⟶ b) (U : X.Opens) (z : Γ(D.obj a, U)) :
      (τ.app b).app U ((D.map f).app U z) = (τ.app a).app U z := by
    have h := τ.naturality f
    simp only [Functor.const_obj_map] at h
    exact congr($(h).app U z)
  refine ⟨IsColimit.ofExistsUnique ?_⟩
  intro s
  let d (U : X.affineOpens) (x : Γ(I.toModules, U.1)) : Γ(s.pt, U.1) :=
    (s.ι.app (a U x)).app U.1 (y U x)
  have hd (U : X.affineOpens) (x : Γ(I.toModules, U.1)) (b : S)
      (z : Γ(D.obj b, U.1)) (hz : (τ.app b).app U.1 z = x) :
      d U x = (s.ι.app b).app U.1 z := by
    obtain ⟨c, hac, hbc⟩ := hab (a U x) b
    have heq : (D.map (homOfLE hac)).app U.1 (y U x) =
        (D.map (homOfLE hbc)).app U.1 z := by
      apply hinj c U.1
      rw [hτ, hτ, hy, hz]
    have hs (b : S) (f : b ⟶ c) (z : Γ(D.obj b, U.1)) :
        (s.ι.app c).app U.1 ((D.map f).app U.1 z) = (s.ι.app b).app U.1 z := by
      have h := s.ι.naturality f
      simp only [Functor.const_obj_map] at h
      exact congr($(h).app U.1 z)
    exact (hs (a U x) (homOfLE hac) (y U x)).symm.trans
      ((congrArg ((s.ι.app c).app U.1) heq).trans (hs b (homOfLE hbc) z))
  have hadd (U : X.affineOpens) (x z : Γ(I.toModules, U.1)) :
      d U (x + z) = d U x + d U z := by
    obtain ⟨c, hxc, hzc⟩ := hab (a U x) (a U z)
    let x' := (D.map (homOfLE hxc)).app U.1 (y U x)
    let z' := (D.map (homOfLE hzc)).app U.1 (y U z)
    have hx' : (τ.app c).app U.1 x' = x := (hτ (homOfLE hxc) U.1 (y U x)).trans (hy U x)
    have hz' : (τ.app c).app U.1 z' = z := (hτ (homOfLE hzc) U.1 (y U z)).trans (hy U z)
    rw [hd U (x + z) c (x' + z') (by rw [map_add, hx', hz']),
      map_add, ← hd U x c x' hx', ← hd U z c z' hz']
  have hsmul (U : X.affineOpens) (r : Γ(X, U.1)) (x : Γ(I.toModules, U.1)) :
      d U (r • x) = r • d U x := by
    rw [hd U (r • x) (a U x) (r • y U x) (by rw [Modules.Hom.app_smul, hy]),
      Modules.Hom.app_smul]
  let dl (U : X.affineOpens) : Γ(I.toModules, U.1) →ₗ[Γ(X, U.1)] Γ(s.pt, U.1) :=
    { toFun := d U, map_add' := hadd U, map_smul' := hsmul U }
  have hres (U V : X.affineOpens) (hVU : V.1 ≤ U.1) (x : Γ(I.toModules, U.1)) :
      d V (I.toModules.presheaf.map (homOfLE hVU).op x) =
        s.pt.presheaf.map (homOfLE hVU).op (d U x) := by
    rw [hd V _ (a U x) ((D.obj (a U x)).presheaf.map (homOfLE hVU).op (y U x))]
    · exact PresheafOfModules.naturality_apply (s.ι.app (a U x)).val (homOfLE hVU).op _
    · exact (PresheafOfModules.naturality_apply (τ.app (a U x)).val
        (homOfLE hVU).op (y U x)).trans
        (congrArg (I.toModules.presheaf.map (homOfLE hVU).op) (hy U x))
  have hb : TopologicalSpace.Opens.IsBasis
      (Set.range (fun U : X.affineOpens ↦ U.1)) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  let B := inducedFunctor (fun U : X.affineOpens ↦ U.1)
  let β : B.op ⋙ I.toModules.presheaf ⟶ B.op ⋙ s.pt.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom (dl U.unop).toAddMonoidHom
      naturality := fun {U V} f ↦ by
        ext x
        exact hres U.unop V.unop (leOfHom f.unop.hom) x }
  let ψ : I.toModules.presheaf ⟶ s.pt.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom I.toModules.presheaf
      ⟨s.pt.presheaf, s.pt.isSheaf⟩ hb β
  have hψ (U : X.affineOpens) (x : Γ(I.toModules, U.1)) :
      ψ.app (.op U.1) x = d U x := by
    exact congr($(TopCat.Sheaf.extend_hom_app I.toModules.presheaf
      ⟨s.pt.presheaf, s.pt.isSheaf⟩ hb β U) x)
  have hcover (U : X.Opens) :
      U ≤ ⨆ V : {V : X.affineOpens // V.1 ≤ U}, V.val.val := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  have hψsmul (U : X.Opens) (r : Γ(X, U)) (x : Γ(I.toModules, U)) :
      ψ.app (.op U) (r • x) = r • ψ.app (.op U) x := by
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨s.pt.presheaf, s.pt.isSheaf⟩
      (fun V : {V : X.affineOpens // V.1 ≤ U} ↦ V.val.val) U
      (fun V ↦ homOfLE V.property) (hcover U) _ _ fun V ↦ ?_
    have hn (x : Γ(I.toModules, U)) :
        s.pt.presheaf.map (homOfLE V.property).op (ψ.app (.op U) x) =
          ψ.app (.op V.val.val) (I.toModules.presheaf.map (homOfLE V.property).op x) :=
      (NatTrans.naturality_apply ψ (homOfLE V.property).op x).symm
    rw [hn, Modules.map_smul, hψ, hsmul, Modules.map_smul, hn, hψ]
  let φ : I.toModules ⟶ s.pt :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            { toFun := ψ.app U
              map_add' := map_add (ψ.app U).hom
              map_smul' := hψsmul U.unop }
          naturality := fun {U V} f ↦ by
            ext x
            exact NatTrans.naturality_apply ψ f x } }
  have hφ (U : X.affineOpens) (x : Γ(I.toModules, U.1)) :
      φ.app U.1 x = d U x := hψ U x
  refine ⟨φ, ?_, ?_⟩
  · intro b
    apply (Modules.toPresheaf X).map_injective
    apply TopCat.Sheaf.hom_ext (D.obj b).presheaf ⟨s.pt.presheaf, s.pt.isSheaf⟩ hb
    intro U
    ext x
    exact (hφ U _).trans (hd U _ b x rfl)
  · intro φ' hφ'
    apply (Modules.toPresheaf X).map_injective
    apply TopCat.Sheaf.hom_ext I.toModules.presheaf ⟨s.pt.presheaf, s.pt.isSheaf⟩ hb
    intro U
    ext x
    have hx := congr($(hφ' (a U x)).app U.1 (y U x))
    change φ'.app U.1 ((τ.app (a U x)).app U.1 (y U x)) = _ at hx
    rw [hy] at hx
    exact hx.trans (hφ U x).symm

end AlgebraicGeometry.Scheme.IdealSheafData
