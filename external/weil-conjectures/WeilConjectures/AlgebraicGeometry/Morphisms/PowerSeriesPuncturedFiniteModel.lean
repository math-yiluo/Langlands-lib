/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionFullyFaithful

/-!
# A coefficient model on the punctured power-series base

## References

* Stacks Project, Tag 0EYA, the construction preceding Psi
* Stacks Project, Tag 0EYA, paragraphs defining W0 and C0 and their comparison on U times_X Y
* Tags 0EY9 and 0EY6(1), (2)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Over the inverse image of the punctured coefficient spectrum, a finite etale
power-series cover has a finite coefficient model of depth two at the closed fibre.
No comparison on the whole power-series spectrum is asserted. -/
theorem exists_power_series_punctured_finite_model
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens) (hproper : V ≠ ⊤)
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    {E : Scheme.{u}} (p : E ⟶ Spec (.of (MvPowerSeries (Fin n) B)))
    [IsFinite p] [Etale (p ∣_ V)]
    (U : (Spec (.of B)).Opens)
    (hU : ∀ x, x ∈ U ↔ x ≠ IsLocalRing.closedPoint B) :
    let t := Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n) (R := B)))
    let W := t ⁻¹ᵁ U
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)), IsFinite g ∧
      (∀ z : Y, g z ∉ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := Y.presheaf.stalk z) (Y.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ W).toScheme ≅ ((Limits.pullback.snd g t) ⁻¹ᵁ W).toScheme,
        e.hom ≫ (Limits.pullback.snd g t) ∣_ W = p ∣_ W := by
  by_cases hV : V = ⊤
  · exact (hproper hV).elim
  let t := Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n) (R := B)))
  let s := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n) (R := B)))
  have hst : s ≫ t = 𝟙 _ := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((MvPowerSeries.constantCoeff (σ := Fin n)).comp MvPowerSeries.C)) = _
    rw [MvPowerSeries.constantCoeff_comp_C]
    exact Spec.map_id _
  let W := t ⁻¹ᵁ U
  have hWV : W ≤ V := by
    intro x hx
    exact haway x ((hU _).mp hx)
  have hEq : s ⁻¹ᵁ W = U := by
    change s ⁻¹ᵁ (t ⁻¹ᵁ U) = U
    rw [← Hom.comp_preimage, hst]
    simp
  let j := (Spec (.of B)).isoOfEq hEq
  let a := s ∣_ W
  have hpa : Etale (p ∣_ W) := by
    have H : IsPullback (E.homOfLE (p.preimage_mono hWV)) (p ∣_ W)
        (p ∣_ V) ((Spec (.of (MvPowerSeries (Fin n) B))).homOfLE hWV) := by
      refine IsPullback.of_right ?_ (morphismRestrict_homOfLE p W V hWV).symm
        (isPullback_morphismRestrict p V).flip
      simpa using (isPullback_morphismRestrict p W).flip
    exact MorphismProperty.of_isPullback (P := @Etale) H inferInstance
  let f := Limits.pullback.snd (p ∣_ W) a ≫ j.hom
  have hboundary : ∀ y : Spec (.of B), y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec (.of B)).presheaf.stalk y) ((Spec (.of B)).presheaf.stalk y) := by
    intro y hy
    have hyclosed : y = IsLocalRing.closedPoint B := by
      simpa only [hU y, not_not] using hy
    subst y
    let e : B ≃+* (Spec (.of B)).presheaf.stalk (IsLocalRing.closedPoint B) :=
      (stalkClosedPointIso (.of B)).symm.commRingCatIsoToRingEquiv
    let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
    obtain ⟨_, hlocal, _, hd⟩ := IsLocalRing.depth_eq_add_of_flat_local
      e.toRingHom (RingHom.Flat.of_bijective e.bijective)
    rw [hd]
    exact hdepth.trans le_self_add
  obtain ⟨Y, g, hg, hgd, e0, he0⟩ :=
    exists_finite_extension_of_depth_two U hboundary f
  have : IsFinite g := hg
  have hgu : Etale (g ∣_ U) := by
    rw [← he0]
    infer_instance
  let r := Limits.pullback.snd g t
  have hb : r ⁻¹ᵁ W ≤ Limits.pullback.fst g t ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    intro x hx
    change t (r x) ∈ U at hx
    change g ((Limits.pullback.fst g t) x) ∈ U
    rwa [← Hom.comp_apply, Limits.pullback.condition, Hom.comp_apply]
  let b := (Limits.pullback.fst g t).resLE (g ⁻¹ᵁ U) (r ⁻¹ᵁ W) hb
  let tu := t ∣_ U
  have H : IsPullback b (r ∣_ W) (g ∣_ U) tu := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict g U).flip
    · simpa [b, tu] using ((isPullback_morphismRestrict r W).flip.paste_horiz
        (IsPullback.of_hasPullback g t))
    · apply (cancel_mono U.ι).mp
      simp only [Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc,
        Limits.pullback.condition]
      simp [r, W, tu]
  have hqr : Etale (r ∣_ W) := MorphismProperty.of_isPullback (P := @Etale) H hgu
  have hatu : a ≫ tu = j.hom := by
    apply (cancel_mono U.ι).mp
    dsimp only [a, tu, j]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, hst, Category.comp_id, isoOfEq_hom_ι]
  let k := Limits.pullback.fst (r ∣_ W) a ≫ b
  have HK : IsPullback k (Limits.pullback.snd (r ∣_ W) a) (g ∣_ U) j.hom := by
    simpa [k, hatu] using (IsPullback.of_hasPullback (r ∣_ W) a).paste_horiz H
  have : IsIso k := HK.isIso_fst_of_isIso
  let α := asIso k
  have hα : α.inv ≫ Limits.pullback.snd (r ∣_ W) a ≫ j.hom = g ∣_ U := by
    rw [← HK.w, ← Category.assoc]
    simp [α]
  have hpW : IsFinite (p ∣_ W) := IsZariskiLocalAtTarget.restrict (P := @IsFinite) inferInstance W
  have hrW : IsFinite (r ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (P := @IsFinite) inferInstance W
  let XP : W.toScheme.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ (p ∣_ W) hpa, hpW⟩
  let XQ : W.toScheme.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ (r ∣_ W) hqr, hrW⟩
  let Fb := FiniteEtale.pullback a
  have hff : ∀ P Q : W.toScheme.FiniteEtale,
      Function.Bijective (Fb.map (X := P) (Y := Q)) := by
    apply finiteEtale_powerSeries_punctured_section_fully_faithful B hdepth n hn W
    intro x
    change x ∈ s ⁻¹ᵁ W ↔ x ≠ IsLocalRing.closedPoint B
    rw [hEq]
    exact hU x
  have : Fb.Full := ⟨fun {P Q} ↦ (hff P Q).2⟩
  have : Fb.Faithful := ⟨fun {P Q} ↦ (hff P Q).1⟩
  let β : Fb.obj XP ≅ Fb.obj XQ := ObjectProperty.isoMk _
    (MorphismProperty.Over.isoMk (e0.symm ≪≫ α.symm) (by
      apply (cancel_mono j.hom).mp
      change ((e0.inv ≫ α.inv) ≫ Limits.pullback.snd (r ∣_ W) a) ≫ j.hom =
        Limits.pullback.snd (p ∣_ W) a ≫ j.hom
      rw [Category.assoc, Category.assoc, hα, ← he0]
      simp [f]))
  let eFE := Fb.preimageIso β
  let forget : W.toScheme.FiniteEtale ⥤ Scheme.{u} :=
    ObjectProperty.ι _ ⋙ Etale.forget W.toScheme ⋙ Over.forget W.toScheme
  exact ⟨Y, g, hg, hgd, forget.mapIso eFE, FiniteEtale.hom_left_comp eFE.hom⟩

end AlgebraicGeometry.Scheme
