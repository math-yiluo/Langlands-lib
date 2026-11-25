/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthOneRestrictionInjective
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Equality detected on the open of a finite depth-two source

## References

* Stacks Project, Tags 0AUK and 0E9I, as used in the converse of Tag 0EY6(2)
* Stacks Project, Tag 01SA
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem depth_eq_of_linearEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (e : M ≃ₗ[R] P) : IsLocalRing.depth (R := R) M = IsLocalRing.depth (R := R) P := by
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

set_option backward.isDefEq.respectTransparency false in
private theorem structure_stalk_linearEquiv (X : Scheme.{u}) (y : X) :
    Nonempty ((TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf y) ≃ₗ[X.presheaf.stalk y]
        X.presheaf.stalk y) := by
  let N := SheafOfModules.unit X.ringCatSheaf
  let D := (TopologicalSpace.OpenNhds.inclusion y).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}
  let e : (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf y) ≃+
      X.presheaf.stalk y :=
    (CategoryTheory.preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (V : X.Opens) (hy : y ∈ V) (b : X.presheaf.obj (Opposite.op V)) :
      e (TopCat.Presheaf.germ N.val.presheaf V y hy b) =
        X.presheaf.germ V y hy b := by
    change (CategoryTheory.Limits.colimit.ι (D ⋙ A)
      (Opposite.op (⟨V, hy⟩ : TopologicalSpace.OpenNhds y)) ≫
        (CategoryTheory.preservesColimitIso A D).inv) b = _
    rw [CategoryTheory.ι_preservesColimitIso_inv]
    rfl
  let ℓ : (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf y) →ₗ[
      X.presheaf.stalk y] X.presheaf.stalk y :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨V, hyV, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨W, hyW, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := X) N.val.presheaf m
        have hy : y ∈ V ⊓ W := ⟨hyV, hyW⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) y hy r,
          ← TopCat.Presheaf.germ_res_apply (X := X) N.val.presheaf
            (homOfLE inf_le_right) y hy m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op r
        let m' : X.presheaf.obj (Opposite.op (V ⊓ W)) :=
          N.val.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op m
        change e (TopCat.Presheaf.germ N.val.presheaf (V ⊓ W) y hy (r' * m')) =
          X.presheaf.germ (V ⊓ W) y hy r' *
            e (TopCat.Presheaf.germ N.val.presheaf (V ⊓ W) y hy m')
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (V ⊓ W) y hy).hom _ _ }
  exact ⟨LinearEquiv.ofBijective ℓ e.bijective⟩

set_option backward.isDefEq.respectTransparency false in
private theorem structure_restriction_injective
    {X : Scheme.{u}} [IsLocallyNoetherian X] (W : X.Opens)
    (hdepth : ∀ y : X, y ∉ W →
      (1 : ℕ∞) ≤ IsLocalRing.depth (R := X.presheaf.stalk y) (X.presheaf.stalk y)) :
    ∀ V : X.Opens, Function.Injective (W.ι.app V) := by
  let N := SheafOfModules.unit X.ringCatSheaf
  have hqc : N.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hsections (V : X.Opens) (_ : IsAffineOpen V) :
      Module.Finite (X.presheaf.obj (Opposite.op V)) (N.val.obj (Opposite.op V)) := by
    change Module.Finite (X.presheaf.obj (Opposite.op V)) (X.presheaf.obj (Opposite.op V))
    infer_instance
  have hd (y : X) (hy : y ∉ W) :
      ∃ hfinite : Module.Finite (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf y),
        letI := hfinite
        (1 : ℕ∞) ≤ IsLocalRing.depth (R := X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf y) := by
    obtain ⟨e⟩ := structure_stalk_linearEquiv X y
    have hfinite := Module.Finite.equiv e.symm
    refine ⟨hfinite, ?_⟩
    have := hfinite
    exact (hdepth y hy).trans_eq (depth_eq_of_linearEquiv e).symm
  intro V
  exact injective_restrictAdjunction_unit_app_of_depth_one W N hqc hsections hd V

set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms to an affine L-scheme agree when they agree on the open
of a finite source whose boundary local rings have depth at least two. -/
theorem hom_eq_of_finite_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsAffineHom p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (f g : F ⟶ E) (hf : f ≫ p = r) (hg : g ≫ p = r)
    (hfg : (r ⁻¹ᵁ U).ι ≫ f = (r ⁻¹ᵁ U).ι ≫ g) : f = g := by
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian r
  let W := r ⁻¹ᵁ U
  have hinj := structure_restriction_injective W (fun z hz ↦
    le_trans (by norm_num : (1 : ℕ∞) ≤ 2) (hF z hz))
  obtain ⟨_, A, _, _, hmap, _⟩ := affine_morphism_relative_spec L
  let FF : ObjectProperty.FullSubcategory (fun Z : Over L ↦ IsAffineHom Z.hom) :=
    ⟨Over.mk r, (inferInstance : IsAffineHom r)⟩
  let EE : ObjectProperty.FullSubcategory (fun Z : Over L ↦ IsAffineHom Z.hom) :=
    ⟨Over.mk p, (inferInstance : IsAffineHom p)⟩
  let af : FF ⟶ EE := ⟨Over.homMk f hf⟩
  let ag : FF ⟶ EE := ⟨Over.homMk g hg⟩
  have he : A.functor.map af.op = A.functor.map ag.op := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    rw [hmap FF EE af V.unop, hmap FF EE ag V.unop]
    apply congrArg (fun t ↦ eqToHom _ ≫ t ≫ eqToHom _)
    have ef : r ⁻¹ᵁ V.unop ≤ f ⁻¹ᵁ (p ⁻¹ᵁ V.unop) := by
      rw [← Hom.comp_preimage, hf]
    have eg : r ⁻¹ᵁ V.unop ≤ g ⁻¹ᵁ (p ⁻¹ᵁ V.unop) := by
      rw [← Hom.comp_preimage, hg]
    have ef' : W.ι ⁻¹ᵁ (r ⁻¹ᵁ V.unop) ≤ (W.ι ≫ f) ⁻¹ᵁ (p ⁻¹ᵁ V.unop) :=
      (TopologicalSpace.Opens.map W.ι.base).monotone ef
    have eg' : W.ι ⁻¹ᵁ (r ⁻¹ᵁ V.unop) ≤ (W.ι ≫ g) ⁻¹ᵁ (p ⁻¹ᵁ V.unop) :=
      (TopologicalSpace.Opens.map W.ι.base).monotone eg
    have hh : (W.ι ≫ f).appLE (p ⁻¹ᵁ V.unop) (W.ι ⁻¹ᵁ (r ⁻¹ᵁ V.unop)) ef' =
        (W.ι ≫ g).appLE (p ⁻¹ᵁ V.unop) (W.ι ⁻¹ᵁ (r ⁻¹ᵁ V.unop)) eg' := by
      congr 1
    rw [← Hom.appLE_comp_appLE W.ι f _ (r ⁻¹ᵁ V.unop) _ ef le_rfl,
      ← Hom.appLE_comp_appLE W.ι g _ (r ⁻¹ᵁ V.unop) _ eg le_rfl] at hh
    have hi : W.ι.appLE (r ⁻¹ᵁ V.unop) (W.ι ⁻¹ᵁ (r ⁻¹ᵁ V.unop)) le_rfl =
        W.ι.app (r ⁻¹ᵁ V.unop) := by
      rw [Hom.appLE]
      change _ ≫ W.toScheme.presheaf.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hi] at hh
    apply CommRingCat.hom_ext
    ext a
    apply hinj (r ⁻¹ᵁ V.unop)
    exact congrArg (fun t ↦ t a) hh
  exact congrArg (fun t ↦ t.unop.hom.left) (A.functor.map_injective he)

end AlgebraicGeometry.Scheme
