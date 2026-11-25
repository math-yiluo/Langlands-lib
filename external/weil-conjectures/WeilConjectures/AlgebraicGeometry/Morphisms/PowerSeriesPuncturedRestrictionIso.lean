/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesThickeningBoundaryDepth
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! Categorical form of the finite thickening restriction comparison.

## References

* Stacks Project, Tag 0EY9
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

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
  have hg (V : X.Opens) (hz : z ∈ V) (b : X.presheaf.obj (Opposite.op V)) :
      e (TopCat.Presheaf.germ N.val.presheaf V z hz b) =
        X.presheaf.germ V z hz b := by
    change (CategoryTheory.Limits.colimit.ι (D ⋙ A)
      (Opposite.op (⟨V, hz⟩ : TopologicalSpace.OpenNhds z)) ≫
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
        let m' : X.presheaf.obj (Opposite.op (V ⊓ W)) :=
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
      Module.Finite (X.presheaf.obj (Opposite.op W)) (N.val.obj (Opposite.op W)) := by
    change Module.Finite (X.presheaf.obj (Opposite.op W)) (X.presheaf.obj (Opposite.op W))
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


/-- The canonical map from a finite power-series thickening to its punctured
restriction is an isomorphism.
-/
theorem isIso_powerSeries_punctured_thickening_restriction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (n : ℕ) :
    IsIso
      ((ΓSpecIso (.of (MvPowerSeries (Fin d) A ⧸ FiniteEtale.Adic.ideal
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n))).inv ≫
        (pullback.snd V.ι (FiniteEtale.Adic.baseMap
          (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n)).appTop) := by
  have _ := hd
  let f := MvPowerSeries.constantCoeff (σ := Fin d) (R := A)
  let q := FiniteEtale.Adic.baseMap f n
  let W := q ⁻¹ᵁ V
  have : IsLocallyNoetherian (FiniteEtale.Adic.base f n) := by
    dsimp [FiniteEtale.Adic.base, f]
    infer_instance
  have hdW := powerSeries_thickening_boundary_depth A hdepth d V hV n
  have hc : IsIso W.ι.c := isIso_inclusion_c_of_depth_two _ W hdW
  have hi : IsIso W.ι.appTop := by
    change IsIso (W.ι.c.app (Opposite.op ⊤))
    infer_instance
  let e := pullbackSymmetry V.ι q ≪≫ pullbackRestrictIsoRestrict q V
  have hfac : e.inv ≫ pullback.snd V.ι q = W.ι := by
    simp [e, W]
  have happ : (pullback.snd V.ι q).appTop ≫ e.inv.appTop = W.ι.appTop := by
    rw [← Scheme.Hom.comp_appTop, hfac]
  have hs : IsIso (pullback.snd V.ι q).appTop := by
    apply (isIso_comp_right_iff _ e.inv.appTop).mp
    rw [happ]
    exact hi
  infer_instance

end AlgebraicGeometry.Scheme
