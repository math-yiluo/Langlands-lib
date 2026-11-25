/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDepthTwoPushforwardHull
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # A coherent depth-two module extending a finite etale algebra

## References

* Stacks Project, Tags 0EY6, 0EBJ, 0EBI and 0E9I
* Stacks Project, Tag 0EY6 proof of (1), Tags 0EBJ and 0EBI
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

private theorem depth_le_of_semilinear_equiv
    {R S M P : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [AddCommGroup M] [AddCommGroup P] [Module R M] [Module S P]
    [Module.Finite R M] [Module.Finite S P]
    (e : R ≃+* S) (a : M ≃+ P) (ha : ∀ r m, a (r • m) = e r • a m) :
    IsLocalRing.depth (R := R) M ≤ IsLocalRing.depth (R := S) P := by
  classical
  cases subsingleton_or_nontrivial P with
  | inl hP =>
    have := hP
    have ht : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P) = ⊤ :=
      Subsingleton.elim _ _
    simp [IsLocalRing.depth, Ideal.depth, ht]
  | inr hP =>
    have := hP
    have : Nontrivial M := a.surjective.nontrivial
    have hM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)).symm
    have hP' : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)).symm
    simp only [IsLocalRing.depth, Ideal.depth, hM, hP', ↓reduceIte]
    apply sSup_le
    rintro n ⟨rs, hreg, hmem, rfl⟩
    apply le_sSup
    refine ⟨rs.map e, ?_, ?_, by simp⟩
    · apply (a.isRegular_congr ?_).mp hreg
      exact List.forall₂_map_right_iff.mpr
        (List.forall₂_same.mpr (fun r _ m ↦ ha r m))
    · intro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
      exact Ideal.mem_map_of_mem e (hmem t ht)

private theorem stalkMap_appIso_inv_germ
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (x : Y) (W : Y.Opens) (hx : x ∈ W) (r : Y.presheaf.obj (op W)) :
    j.stalkMap x (Z.presheaf.germ (j ''ᵁ W) (j x) ⟨x, hx, rfl⟩
      ((j.appIso W).inv r)) = Y.presheaf.germ W x hx r := by
  rw [Hom.germ_stalkMap_apply]
  have h := ConcreteCategory.congr_hom (Hom.appIso_inv_app j W) r
  change j.app (j ''ᵁ W) ((j.appIso W).inv r) = _ at h
  rw [h]
  exact Y.presheaf.germ_res_apply _ x _ r

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem restrict_stalk_smul
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (M : Z.Modules) (x : Y) :
    let a : (TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y) (M.restrict j).val.presheaf x)
        →+ (TopCat.Presheaf.stalk (C := Ab.{u}) (X := Z) M.val.presheaf (j x)) :=
      ((Modules.restrictStalkNatIso j x).hom.app M).hom
    ∀ (r : Y.presheaf.stalk x)
        (m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y) (M.restrict j).val.presheaf x),
      a (r • m) = (asIso (j.stalkMap x)).inv r • a m := by
  dsimp only
  intro r m
  obtain ⟨W, hxW, r, rfl⟩ := Y.presheaf.exists_germ_eq r
  obtain ⟨V, hVW, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (X := Y) (C := Ab.{u})
    (M.restrict j).val.presheaf m hxW
  rw [← Y.presheaf.germ_res_apply (homOfLE hVW) x hxV r]
  rw [← PresheafOfModules.germ_smul (R := Y.presheaf)
    (M.restrict j).val x V hxV (Y.presheaf.map (homOfLE hVW).op r) m]
  have hm (t : (M.restrict j).val.presheaf.obj (op V)) :
      ((Modules.restrictStalkNatIso j x).hom.app M).hom
          (TopCat.Presheaf.germ (X := Y) (C := Ab.{u})
            (M.restrict j).val.presheaf V x hxV t) =
        TopCat.Presheaf.germ (X := Z) (C := Ab.{u})
          M.val.presheaf (j ''ᵁ V) (j x) ⟨x, hxV, rfl⟩ t :=
    ConcreteCategory.congr_hom (Modules.germ_restrictStalkNatIso_hom_app j x M hxV) t
  erw [hm, hm]
  have hr (t : Y.presheaf.obj (op V)) :
      (asIso (j.stalkMap x)).inv (Y.presheaf.germ V x hxV t) =
        Z.presheaf.germ (j ''ᵁ V) (j x) ⟨x, hxV, rfl⟩ ((j.appIso V).inv t) := by
    apply (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1
    have hi := ConcreteCategory.congr_hom (Iso.inv_hom_id (asIso (j.stalkMap x)))
      (Y.presheaf.germ V x hxV t)
    change j.stalkMap x ((asIso (j.stalkMap x)).inv
      (Y.presheaf.germ V x hxV t)) = Y.presheaf.germ V x hxV t at hi
    rw [hi]
    exact (stalkMap_appIso_inv_germ j x V hxV t).symm
  rw [hr]
  exact M.val.germ_smul (j x) (j ''ᵁ V) ⟨x, hxV, rfl⟩ _ m

/-- The underlying finite etale module admits a coherent extension of depth two. -/
theorem exists_depth_two_coherent_module_extension
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f] :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    ∃ N : L.Modules,
      N.IsQuasicoherent ∧
      (∀ V : L.Opens, IsAffineOpen V →
        Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V))) ∧
      (∀ y : L, y ∉ U →
        ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
          letI := hfinite
          (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) ∧
      Nonempty (Modules.restrict N U.ι ≅ Modules.restrict B.toModule U.ι) := by
  let g := f ≫ U.ι
  let B : L.CommAlgebraSheaf := Under.mk
    (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
  have hlocal (V : L.Opens) (hV : IsAffineOpen V) :=
    affine_depth_two_pushforward_hull U hboundary f V hV
  refine ⟨B.toModule, ?_, ?_, ?_, ⟨Iso.refl _⟩⟩
  · apply Modules.isQuasicoherent_of_iSup_opensRange_eq_top B.toModule
      (fun V : L.affineOpens ↦ V.2.fromSpec) Modules.iSup_opensRange_fromSpec_eq_top
    intro V
    have := (hlocal V.1 V.2).1
    exact Modules.presentationOfIsIsoFromTildeΓ _
  · intro V hV
    have := (hlocal V hV).2.1
    exact Modules.finite_sections_of_finite_sections_restrict_fromSpec B.toModule hV
  · intro y hy
    obtain ⟨V, hV, hyV⟩ : ∃ V : L.Opens, ∃ hV : IsAffineOpen V, y ∈ V := by
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, _⟩ :=
        L.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      exact ⟨V, hV, hyV⟩
    have hyrange : y ∈ Set.range hV.fromSpec := by
      change y ∈ hV.fromSpec.opensRange
      rwa [hV.opensRange_fromSpec]
    obtain ⟨x, hx⟩ := hyrange
    obtain ⟨hfinite, hdepth⟩ := (hlocal V hV).2.2 x (by simpa [hx] using hy)
    have := hfinite
    let j := hV.fromSpec
    let E := (Modules.restrictStalkNatIso j x).app B.toModule
    let e := (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv
    let a : (TopCat.Presheaf.stalk (C := Ab.{u})
          (Modules.restrict B.toModule j).val.presheaf x) ≃+
        (TopCat.Presheaf.stalk (C := Ab.{u}) B.toModule.val.presheaf (j x)) :=
      AddEquiv.ofBijective E.hom.hom (ConcreteCategory.bijective_of_isIso E.hom)
    have ha : ∀ r m, a (r • m) = e r • a m := restrict_stalk_smul j B.toModule x
    let t : (TopCat.Presheaf.stalk (C := Ab.{u}) (Modules.restrict B.toModule j).val.presheaf x)
        →ₛₗ[e.toRingHom]
        (TopCat.Presheaf.stalk (C := Ab.{u}) B.toModule.val.presheaf (j x)) :=
      { toFun := a
        map_add' := a.map_add
        map_smul' := ha }
    have hfinite' := Module.Finite.of_surjective t a.surjective
    rw [← hx]
    exact ⟨hfinite', hdepth.trans (depth_le_of_semilinear_equiv e a ha)⟩

end AlgebraicGeometry.Scheme
