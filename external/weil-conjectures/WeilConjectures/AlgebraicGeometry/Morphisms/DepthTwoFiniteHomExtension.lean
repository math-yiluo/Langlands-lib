/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Extension of morphisms from finite depth-two schemes

## References

* Stacks Project, Tag 0EY6, converse in the proof of (2), using Tags 0AUK and 0E9I
* Stacks Project, Tag 01SA
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

section PrivateHelpers

open Opposite TopologicalSpace

private noncomputable abbrev algebraOf {X S : Scheme.{u}} (f : X ⟶ S) :
    S.CommAlgebraSheaf := Under.mk
  (⟨f.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)
private noncomputable def algebraMapOf {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : X ⟶ Y) (w : h ≫ g = f) : algebraOf g ⟶ algebraOf f := by
  refine Under.homMk ⟨{
    app := fun V ↦ h.appLE (g ⁻¹ᵁ V.unop) (f ⁻¹ᵁ V.unop)
      (by rw [← w, Hom.comp_preimage])
    naturality := ?_ }⟩ ?_
  · intro U V i
    change Y.presheaf.map ((Opens.map g.base).map i.unop).op ≫ _ =
      _ ≫ X.presheaf.map ((Opens.map f.base).map i.unop).op
    simp only [Hom.map_appLE, Hom.appLE_map]
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change g.app V.unop ≫ h.appLE _ _ _ = f.app V.unop
    rw [← Hom.comp_appLE]
    exact (Hom.congr_app w.symm V.unop).symm
private theorem iso_algebraMapOf_inclusion {S X : Scheme.{u}} (f : X ⟶ S)
    (V : X.Opens) [IsIso V.ι.c] :
    IsIso (algebraMapOf (V.ι ≫ f) f V.ι rfl) := by
  have happ (W : S.Opensᵒᵖ) :
      IsIso ((algebraMapOf (V.ι ≫ f) f V.ι rfl).right.hom.app W) := by
    change IsIso (V.ι.appLE (f ⁻¹ᵁ W.unop) ((V.ι ≫ f) ⁻¹ᵁ W.unop) _)
    unfold Hom.appLE
    have : IsIso (V.ι.app (f ⁻¹ᵁ W.unop)) := inferInstance
    have : IsIso (homOfLE
      (show (V.ι ≫ f) ⁻¹ᵁ W.unop ≤ V.ι ⁻¹ᵁ (f ⁻¹ᵁ W.unop) by
        rw [Hom.comp_preimage])) :=
      homOfLE_isIso_of_eq _ (Hom.comp_preimage _ _ _)
    infer_instance
  let := happ
  have : IsIso (algebraMapOf (V.ι ≫ f) f V.ι rfl).right.hom :=
    NatIso.isIso_of_isIso_app _
  have : IsIso ((TopCat.Sheaf.forget CommRingCat S.toTopCat).map
      (algebraMapOf (V.ι ≫ f) f V.ι rfl).right) := by
    change IsIso (algebraMapOf (V.ι ≫ f) f V.ι rfl).right.hom
    assumption
  have : IsIso (algebraMapOf (V.ι ≫ f) f V.ι rfl).right :=
    isIso_of_reflects_iso _ (TopCat.Sheaf.forget CommRingCat S.toTopCat)
  have : IsIso ((Under.forget S.sheaf).map (algebraMapOf (V.ι ≫ f) f V.ι rfl)) := by
    change IsIso (algebraMapOf (V.ι ≫ f) f V.ι rfl).right
    assumption
  exact isIso_of_reflects_iso _ (Under.forget S.sheaf)
private theorem affine_over_ext {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] (h h' : X ⟶ Y) (w : h ≫ g = f) (w' : h' ≫ g = f)
    (he : ∀ U : S.affineOpens,
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Hom.comp_preimage]) =
      h'.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w', Hom.comp_preimage])) : h = h' := by
  apply hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show f x ∈ (⊤ : S.Opens) from trivial) isOpen_univ
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  have hh : h.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w, Hom.comp_preimage]) =
    h'.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w', Hom.comp_preimage]) := by
    apply ext_of_isAffine
    simp only [Hom.appTop, Hom.resLE_app_top]
    rw [he ⟨U, hU⟩]
  simpa only [Hom.resLE_comp_ι] using congrArg (· ≫ (g ⁻¹ᵁ U).ι) hh

private theorem exists_over_map_of_algebra {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [IsAffineHom g] (α : (algebraOf g : S.CommAlgebraSheaf) ⟶ algebraOf f) :
    ∃ (h : X ⟶ Y) (w : h ≫ g = f), ∀ U : S.affineOpens,
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Hom.comp_preimage]) = α.right.hom.app (op U.1) := by
  obtain ⟨k, hw, hc, ha⟩ := affine_algebra_local_maps f g α
  let 𝒰 := X.openCoverOfIsOpenCover (fun U : S.affineOpens ↦ f ⁻¹ᵁ U.1)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  let h : X ⟶ Y := 𝒰.glueMorphisms k hc
  have hi (U : S.affineOpens) : (f ⁻¹ᵁ U.1).ι ≫ h = k U :=
    𝒰.ι_glueMorphisms k hc U
  have w : h ≫ g = f := by
    apply 𝒰.hom_ext
    intro U
    change (f ⁻¹ᵁ U.1).ι ≫ h ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f
    rw [← Category.assoc, hi, hw]
  refine ⟨h, w, ?_⟩
  intro U
  have e : ⊤ ≤ k U ⁻¹ᵁ (g ⁻¹ᵁ U.1) := by
    rw [← Hom.comp_preimage, hw, Hom.comp_preimage]
    simp
  have ea := ha U e
  simp only [← hi U] at ea
  rw [Hom.comp_appLE] at ea
  simp only [Opens.ι_appLE] at ea
  apply (cancel_mono (f ⁻¹ᵁ U.1).topIso.inv).mp
  simp only [Hom.appLE, Opens.topIso_inv, Category.assoc,
    ← Functor.map_comp] at ea ⊢
  convert ea using 1
  congr 1


private theorem depth_equiv_local {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (e : M ≃ₗ[R] P) :
      IsLocalRing.depth (R := R) M = IsLocalRing.depth (R := R) P := by
  have hmap : (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).map e.toLinearMap =
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have htop : (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤) ↔
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R P) = ⊤) := by
    constructor
    · intro h
      rw [← hmap, h]
      simp
    · intro h
      rw [← hmap] at h
      exact (Submodule.map_eq_top_iff.mp h)
  unfold IsLocalRing.depth Ideal.depth
  split_ifs with hM hP hP
  · rfl
  · exact (hP (htop.mp hM)).elim
  · exact (hM (htop.mpr hP)).elim
  · congr 1
    ext n
    constructor
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mp hreg, hmem, rfl⟩
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mpr hreg, hmem, rfl⟩


private theorem algebraMapOf_comp {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (a : X ⟶ Y) (b : Y ⟶ Z) (wa : a ≫ g = f) (wb : b ≫ h = g) :
    algebraMapOf f h (a ≫ b) (by rw [Category.assoc, wb, wa]) =
      algebraMapOf g h b wb ≫ algebraMapOf f g a wa := by
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (a ≫ b).appLE _ _ _ = b.appLE _ _ _ ≫ a.appLE _ _ _
  rw [Hom.appLE_comp_appLE]

private theorem algebraMapOf_injective {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g]
    (a b : X ⟶ Y) (wa : a ≫ g = f) (wb : b ≫ g = f)
    (hab : algebraMapOf f g a wa = algebraMapOf f g b wb) : a = b := by
  apply affine_over_ext f g a b wa wb
  intro V
  exact congrArg (fun t ↦ t.right.hom.app (op V.1)) hab

private theorem exists_of_algebraMap {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g]
    (α : algebraOf g ⟶ algebraOf f) :
    ∃ (a : X ⟶ Y) (wa : a ≫ g = f), algebraMapOf f g a wa = α := by
  obtain ⟨a, wa, ha⟩ := exists_over_map_of_algebra f g α
  refine ⟨a, wa, ?_⟩
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (B := fun U : S.affineOpens ↦ U.1)
    (by
      change Opens.IsBasis (Set.range (fun U : S.affineOpens ↦ U.1))
      rw [show Set.range (fun U : S.affineOpens ↦ U.1) = S.affineOpens by
        ext V
        constructor
        · rintro ⟨U, rfl⟩
          exact U.2
        · intro hV
          exact ⟨⟨V, hV⟩, rfl⟩]
      exact S.isBasis_affineOpens)
  exact ha

private theorem extend_of_isIso_inclusion_c {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g]
    (V : X.Opens) [IsIso V.ι.c]
    (b : V.toScheme ⟶ Y) (wb : b ≫ g = V.ι ≫ f) :
    ∃ a : X ⟶ Y, a ≫ g = f ∧ V.ι ≫ a = b := by
  let β := algebraMapOf (V.ι ≫ f) f V.ι rfl
  have : IsIso β := iso_algebraMapOf_inclusion f V
  let γ := algebraMapOf (V.ι ≫ f) g b wb
  obtain ⟨a, wa, ha⟩ := exists_of_algebraMap f g (γ ≫ inv β)
  refine ⟨a, wa, ?_⟩
  apply algebraMapOf_injective (V.ι ≫ f) g (V.ι ≫ a) b
    (by rw [Category.assoc, wa]) wb
  rw [algebraMapOf_comp (V.ι ≫ f) f g V.ι a rfl wa, ha]
  simp [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem unit_stalk_equiv (X : Scheme.{u}) (z : X) :
    Nonempty ((TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf z) ≃ₗ[X.presheaf.stalk z]
      X.presheaf.stalk z) := by
  let N := SheafOfModules.unit X.ringCatSheaf
  let D := (TopologicalSpace.OpenNhds.inclusion z).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}
  let e : (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf z) ≃+
      X.presheaf.stalk z :=
    (CategoryTheory.preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (V : X.Opens) (hz : z ∈ V) (b : X.presheaf.obj (op V)) :
      e (TopCat.Presheaf.germ N.val.presheaf V z hz b) =
        X.presheaf.germ V z hz b := by
    change (CategoryTheory.Limits.colimit.ι (D ⋙ A)
      (op (⟨V, hz⟩ : TopologicalSpace.OpenNhds z)) ≫
        (CategoryTheory.preservesColimitIso A D).inv) b = _
    rw [CategoryTheory.ι_preservesColimitIso_inv]
    rfl
  let ℓ : (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf z)
      →ₗ[X.presheaf.stalk z] X.presheaf.stalk z :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨V, hzV, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨W, hzW, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.val.presheaf m
        have hz : z ∈ V ⊓ W := ⟨hzV, hzW⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) z hz r,
          ← TopCat.Presheaf.germ_res_apply N.val.presheaf
            (homOfLE inf_le_right) z hz m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op r
        let m' : X.presheaf.obj (op (V ⊓ W)) :=
          N.val.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op m
        change e (TopCat.Presheaf.germ N.val.presheaf (V ⊓ W) z hz (r' * m')) =
          X.presheaf.germ (V ⊓ W) z hz r' *
            e (TopCat.Presheaf.germ N.val.presheaf (V ⊓ W) z hz m')
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (V ⊓ W) z hz).hom _ _ }
  exact ⟨LinearEquiv.ofBijective ℓ e.bijective⟩

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_inclusion_c_of_depth_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (V : X.Opens)
    (hd : ∀ z : X, z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := X.presheaf.stalk z) (X.presheaf.stalk z)) :
    IsIso V.ι.c := by
  let N := SheafOfModules.unit X.ringCatSheaf
  have hqc : N.IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := X.ringCatSheaf)
  have hsections (W : X.Opens) (_ : IsAffineOpen W) :
      Module.Finite (X.presheaf.obj (op W)) (N.val.obj (op W)) := by
    change Module.Finite (X.presheaf.obj (op W)) (X.presheaf.obj (op W))
    infer_instance
  have hdepth (z : X) (hz : z ∉ V) :
      ∃ hfinite : Module.Finite (X.presheaf.stalk z)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf z),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := X.presheaf.stalk z)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf z) := by
    obtain ⟨e⟩ := unit_stalk_equiv X z
    have hf := Module.Finite.equiv e.symm
    refine ⟨hf, ?_⟩
    exact (hd z hz).trans_eq (depth_equiv_local e).symm
  have := isIso_restrictAdjunction_unit_of_depth_two V N hqc hsections hdepth
  have happ (W : X.Opensᵒᵖ) : IsIso (V.ι.c.app W) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have h := ConcreteCategory.bijective_of_isIso
      (((Modules.restrictAdjunction V.ι).unit.app N).app W.unop)
    rw [Modules.restrictAdjunction_unit_app_app] at h
    exact h
  let := happ
  exact NatIso.isIso_of_isIso_app _


end PrivateHelpers

/-- Morphisms over an open into an affine L-scheme extend from a finite source
with boundary depth at least two. -/
theorem exists_hom_of_finite_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsAffineHom p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (a : (r ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme)
    (ha : a ≫ p ∣_ U = r ∣_ U) :
    ∃ f : F ⟶ E, f ≫ p = r ∧ (r ⁻¹ᵁ U).ι ≫ f = a ≫ (p ⁻¹ᵁ U).ι := by
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian r
  have : IsIso (r ⁻¹ᵁ U).ι.c :=
    isIso_inclusion_c_of_depth_two F (r ⁻¹ᵁ U) hF
  apply extend_of_isIso_inclusion_c r p (r ⁻¹ᵁ U) (a ≫ (p ⁻¹ᵁ U).ι)
  rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, ha,
    morphismRestrict_ι]

end AlgebraicGeometry.Scheme
