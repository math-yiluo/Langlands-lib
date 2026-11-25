/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The ideal of a closed immersion on stalks

Source: Stacks Project, Modules, Lemma 08KS and Lemma 01AG.
(blueprint: lem-weil-pbc-closed-immersion-ideal-stalk-range).
-/

@[expose] public section

universe w
open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem ideal_stalk_map_germ {Y : Scheme.{w}} (x : Y) {M N : Y.Modules}
    (f : M ⟶ N) (U : Y.Opens) (hx : x ∈ U) (m : M.val.obj (op U)) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace x).map f
      (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
    TopCat.Presheaf.germ N.val.presheaf U x hx ((f.val.app (op U)) m) := by
  change RingedSpace.stalkAddMap Y.toRingedSpace x f _ = _
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- The stalk ideal is the kernel of the local ring map on the image, and the whole
ring off the image. The comparison `e` identifies structure-module germs with ring germs.
Source: Stacks Project, Modules, Lemma 08KS, using Lemma 01AG.
(blueprint: lem-weil-pbc-closed-immersion-ideal-stalk-range).

Proof: On affine opens the range of the ideal inclusion is the kernel of `i.app`,
by `range_toModulesι_app` and the definition of `i.ker`. At a point of the image,
represent a ring germ on an affine neighbourhood. Its image under the local ring
map is zero precisely when, after shrinking the corresponding neighbourhood in Z,
the image section is zero. The closed embedding allows that neighbourhood to be
replaced by the inverse image of a smaller open in Y. Shrink further to an affine
open in Y; the section now lies in the affine kernel ideal and lifts to an ideal
section. This proves both inclusions of the stalk range equality. Off the closed
image choose an affine neighbourhood disjoint from it. Its inverse image is empty,
so the map on sections has zero target and its kernel is the whole ring. Every
ring germ therefore lifts to an ideal germ. The formulas for `e` and the stalk map
send these lifted germs to the original ring germs. -/
theorem closedImmersion_ideal_stalk_range {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (x : Y)
    (e : (RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj
      (SheafOfModules.unit Y.ringCatSheaf) ≅
        ModuleCat.of (Y.presheaf.stalk x) (Y.presheaf.stalk x))
    (he : ∀ (U : Y.Opens) (hx : x ∈ U) (r : Γ(Y, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit Y.ringCatSheaf).val.presheaf
        U x hx r) = Y.presheaf.germ U x hx r) :
    let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace x
    (∀ (z : Z) (h : x = i.base z),
      LinearMap.range (S.map i.ker.toModulesι ≫ e.hom).hom =
        h.symm ▸ RingHom.ker (i.stalkMap z).hom) ∧
    (x ∉ Set.range i.base →
      LinearMap.range (S.map i.ker.toModulesι ≫ e.hom).hom = ⊤) := by
  classical
  dsimp only
  have hg (U : Y.Opens) (hx : x ∈ U) (m : i.ker.toModules.val.obj (op U)) :
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace x).map i.ker.toModulesι ≫ e.hom |>
        fun f ↦ f (TopCat.Presheaf.germ i.ker.toModules.val.presheaf U x hx m) =
          Y.presheaf.germ U x hx (i.ker.toModulesι.app U m) := by
    change e.hom ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).map
      i.ker.toModulesι _) = _
    rw [ideal_stalk_map_germ, he]
    rfl
  have hlift (U : Y.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (r : Γ(Y, U))
      (hr : i.app U r = 0) :
      Y.presheaf.germ U x hx r ∈ LinearMap.range
        ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).map
          i.ker.toModulesι ≫ e.hom).hom := by
    have hi : r ∈ i.ker.ideal ⟨U, hU⟩ := by
      rw [Scheme.Hom.ker_apply]
      exact hr
    have hi' : r ∈ (i.ker.ideal ⟨U, hU⟩ : Set Γ(Y, U)) := hi
    rw [← i.ker.range_toModulesι_app ⟨U, hU⟩] at hi'
    obtain ⟨m, hm⟩ := hi'
    exact ⟨TopCat.Presheaf.germ i.ker.toModules.val.presheaf U x hx m,
      (hg U hx m).trans (congrArg (Y.presheaf.germ U x hx) hm)⟩
  constructor
  · intro z h
    subst x
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      obtain ⟨U, hx, hU, m, rfl⟩ :=
        TopCat.Presheaf.exists_mem_germ_eq_of_isBasis Y.isBasis_affineOpens
          i.ker.toModules.val.presheaf (i.base z) m
      rw [hg]
      change i.stalkMap z (Y.presheaf.germ U (i.base z) hx _) = 0
      rw [Scheme.Hom.germ_stalkMap_apply]
      have hi : i.ker.toModulesι.app U m ∈ i.ker.ideal ⟨U, hU⟩ := by
        change i.ker.toModulesι.app U m ∈ (i.ker.ideal ⟨U, hU⟩ : Set Γ(Y, U))
        rw [← i.ker.range_toModulesι_app ⟨U, hU⟩]
        exact ⟨m, rfl⟩
      have hz := i.ideal_ker_le ⟨U, hU⟩ hi
      change i.app U (i.ker.toModulesι.app U m) = 0 at hz
      rw [hz, map_zero]
    · intro r hr
      obtain ⟨U, hx, r, rfl⟩ := Y.presheaf.exists_germ_eq r
      change i.stalkMap z (Y.presheaf.germ U (i.base z) hx r) = 0 at hr
      rw [Scheme.Hom.germ_stalkMap_apply] at hr
      have hr' : Z.presheaf.germ (i ⁻¹ᵁ U) z hx (i.app U r) =
          Z.presheaf.germ (i ⁻¹ᵁ U) z hx 0 := by simpa using hr
      obtain ⟨W, hzW, j, _, hj⟩ := Z.presheaf.germ_eq z hx hx (i.app U r) 0 hr'
      obtain ⟨V, hV, hVW⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W.isOpen
      let V' : Y.Opens := ⟨V, hV⟩
      have hzV : i.base z ∈ V' := by
        change z ∈ i.base ⁻¹' V
        rw [hVW]
        exact hzW
      obtain ⟨_, ⟨A, hA, rfl⟩, hzA, hAV⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open
          (show i.base z ∈ V' ⊓ U from ⟨hzV, hx⟩) (V' ⊓ U).isOpen
      have hAU : A ≤ U := fun y hy ↦ (hAV hy).2
      have hAW : i ⁻¹ᵁ A ≤ W := by
        intro y hy
        change y ∈ (W : Set Z)
        rw [← hVW]
        exact (hAV hy).1
      let r' := Y.presheaf.map (homOfLE hAU).op r
      have hzero : i.app A r' = 0 := by
        have hj' := congrArg (Z.presheaf.map (homOfLE hAW).op) hj
        simp only [map_zero] at hj'
        have hn := ConcreteCategory.congr_hom (i.naturality (homOfLE hAU).op) r
        simp only [ConcreteCategory.comp_apply] at hn
        dsimp only [r']
        rw [hn]
        have hmaps : Z.presheaf.map j.op ≫ Z.presheaf.map (homOfLE hAW).op =
            Z.presheaf.map ((Opens.map i.base).map (homOfLE hAU)).op := by
          rw [← Z.presheaf.map_comp]
          congr 1
        simpa only [← ConcreteCategory.comp_apply, Category.assoc, hmaps,
          Quiver.Hom.unop_op] using hj'
      rw [← Y.presheaf.germ_res_apply (homOfLE hAU) (i.base z) hzA r]
      exact hlift A hA hzA r' hzero
  · intro hx
    apply top_unique
    intro r _
    let V : Y.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨U, hUV, hxU, r, rfl⟩ := Y.presheaf.exists_le_germ_eq r (show x ∈ V from hx)
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    let r' := Y.presheaf.map (homOfLE hAU).op r
    have hempty : i ⁻¹ᵁ A = ⊥ := by
      ext z
      exact ⟨fun hz ↦ (hUV (hAU hz)) ⟨z, rfl⟩, False.elim⟩
    have hzero : i.app A r' = 0 := by
      have hsub := TopCat.Sheaf.isTerminalOfEqEmpty Z.sheaf hempty
      exact (CommRingCat.subsingleton_of_isTerminal hsub).elim _ _
    rw [← Y.presheaf.germ_res_apply (homOfLE hAU) x hxA r]
    exact hlift A hA hxA r' hzero

end
end AlgebraicGeometry.Scheme.Modules
