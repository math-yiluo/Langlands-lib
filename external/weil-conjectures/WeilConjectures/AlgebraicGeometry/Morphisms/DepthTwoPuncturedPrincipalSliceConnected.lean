/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.LTSeries
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Connectedness of a depth-two puncture and its principal slice

## References

* Stacks Project, Tags 0E9I, 0BK0, 00LK and 00KW
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
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

private theorem depth_le_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    IsLocalRing.depth (R := R) R ≤ IsLocalRing.depth (R := S) S := by
  classical
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  unfold IsLocalRing.depth Ideal.depth
  simp only [Ideal.smul_eq_mul, Ideal.mul_top,
    ite_eq_right (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    ite_eq_right (IsLocalRing.maximalIdeal.isMaximal S).ne_top]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · exact (e.toAddEquiv.isRegular_congr <| List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ x ↦ e.map_mul r x).mp hreg
  · intro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact IsLocalRing.map_maximalIdeal_le e.toRingHom
      (Ideal.mem_map_of_mem _ (hmem r hr))

set_option backward.isDefEq.respectTransparency false in
private theorem puncture_globalSections_bijective
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    Function.Bijective W.ι.appTop := by
  let X := Spec (.of R)
  let N := SheafOfModules.unit X.ringCatSheaf
  have hqc : N.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hsections (V : X.Opens) (_ : IsAffineOpen V) :
      Module.Finite (X.presheaf.obj (op V)) (N.val.obj (op V)) := by
    change Module.Finite (X.presheaf.obj (op V)) (X.presheaf.obj (op V))
    infer_instance
  have hd (y : X) (hy : y ∉ W) :
      ∃ hfinite : Module.Finite (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.val.presheaf y) := by
    have heqy : y = IsLocalRing.closedPoint R := by
      by_contra h
      exact hy ((hW y).mpr h)
    subst y
    obtain ⟨e⟩ := structure_stalk_linearEquiv X (IsLocalRing.closedPoint R)
    have hf := Module.Finite.equiv e.symm
    refine ⟨hf, ?_⟩
    have := hf
    rw [depth_eq_of_linearEquiv e]
    exact hdepth.trans (depth_le_of_ringEquiv
      (stalkClosedPointIso (.of R)).symm.commRingCatIsoToRingEquiv)
  have hη := isIso_restrictAdjunction_unit_of_depth_two W N hqc hsections hd
  have := hη
  exact ConcreteCategory.bijective_of_isIso (((Modules.restrictAdjunction W.ι).unit.app N).app ⊤)

/-- A depth-two puncture is connected and meets each principal closed slice. -/
theorem depth_two_punctured_principal_slice_connected
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {g})))
    ConnectedSpace W.toScheme ∧ Nonempty (j ⁻¹ᵁ W).toScheme  := by
  classical
  dsimp only
  have hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R := by
    have hb := IsLocalRing.depth_le_supportDim (R := R) R
    rw [Module.supportDim_self_eq_ringKrullDim] at hb
    exact (WithBot.coe_le_coe.mpr hdepth).trans hb
  obtain ⟨p, hp⟩ := (Order.le_krullDim_iff (α := PrimeSpectrum R) (n := 2)).mp hdim
  let p₀ := p ⟨0, by omega⟩
  let p₁ := p ⟨1, by omega⟩
  let p₂ := p ⟨2, by omega⟩
  have h₀ : p₀ < p₁ := p.strictMono (by change (0 : ℕ) < 1; omega)
  have h₁₂ : p₁ < p₂ := p.strictMono (by change (1 : ℕ) < 2; omega)
  have h₁ : p₁ < IsLocalRing.closedPoint R :=
    h₁₂.trans_le (IsLocalRing.le_maximalIdeal_of_isPrime p₂.asIdeal)
  obtain ⟨q, hgq, _, hqm⟩ := PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal h₀ h₁ hg
  let I : Ideal R := Ideal.span {g}
  have hqI : q ∈ PrimeSpectrum.zeroLocus I := (Ideal.span_singleton_le_iff_mem q.asIdeal).mpr hgq
  have hqrange : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hqI
  obtain ⟨x, hx⟩ := hqrange
  have hxW : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) x ∈ W := by
    apply (hW _).mpr
    change PrimeSpectrum.comap (Ideal.Quotient.mk I) x ≠ IsLocalRing.closedPoint R
    rw [hx]
    exact fun h ↦ hqm.ne (congrArg PrimeSpectrum.asIdeal h)
  have hn : Nonempty ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹ᵁ W).toScheme :=
    ⟨⟨x, hxW⟩⟩
  have : Nonempty W.toScheme :=
    ⟨((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ∣_ W) ⟨x, hxW⟩⟩
  have hb := puncture_globalSections_bijective R hdepth W hW
  have : Nontrivial Γ(W.toScheme, ⊤) :=
    (W.toScheme.presheaf.germ ⊤
      (Classical.choice ‹Nonempty W.toScheme›) trivial).hom.domain_nontrivial
  have : IsLocalRing Γ(W.toScheme, ⊤) :=
    IsLocalRing.of_surjective' ((ΓSpecIso (.of R)).inv ≫ W.ι.appTop).hom
      (hb.2.comp (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).inv).2)
  refine ⟨?_, hn⟩
  exact (connectedSpace_iff_isIdempotentElem W.toScheme).mpr
    (fun e he ↦ IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem he)

end AlgebraicGeometry.Scheme
