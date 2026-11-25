/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite etale restriction on the fixed formal test

## References

* Stacks Project, Tags 035I and 03GV (relative normalization and smooth base change), Tag 0EYJ (the
  punctured local-base calculation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

private theorem normalization_open_property (Q : MorphismProperty Scheme.{u})
    [Q.RespectsIso] {C : Scheme.{u}} (U : C.Opens)
    (P : U.toScheme.FiniteEtale) [QuasiCompact U.ι] (hP : Q P.obj.hom) :
    letI : IsFinite P.obj.hom := P.property
    Q ((P.obj.hom ≫ U.ι).fromNormalization ∣_ U) := by
  let : IsFinite P.obj.hom := P.property
  let f := P.obj.hom ≫ U.ι
  let k := pullback.snd f U.ι
  have H : IsPullback (𝟙 P.obj.left) P.obj.hom f U.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [f]⟩
  have hkf : IsFinite k := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) H.isoPullback.hom]
    simpa only [k, H.isoPullback_hom_snd] using P.property
  let := hkf
  have hke : Q k := by
    rw [← Q.cancel_left_of_respectsIso H.isoPullback.hom]
    simpa only [k, H.isoPullback_hom_snd] using hP
  have hkn : Q k.fromNormalization := by
    have he : k.fromNormalization = inv k.toNormalization ≫ k := by
      apply (cancel_epi k.toNormalization).mp
      simp only [k.toNormalization_fromNormalization, IsIso.hom_inv_id_assoc]
    rw [he, Q.cancel_left_of_respectsIso]
    exact hke
  let e := f.normalizationPullback U.ι
  have he : IsIso e := inferInstance
  let := he
  have hbase : Q (pullback.snd f.fromNormalization U.ι) := by
    have hh : pullback.snd f.fromNormalization U.ι = inv e ≫ k.fromNormalization := by
      rw [← f.normalizationPullback_snd U.ι]
      simp [e]
    rw [hh, Q.cancel_left_of_respectsIso]
    exact hkn
  let Hn := (isPullback_morphismRestrict f.fromNormalization U).flip
  rw [← Hn.isoPullback_hom_snd, Q.cancel_left_of_respectsIso]
  exact hbase

private theorem property_pullback_open (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] {X Y B : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (U : B.Opens) (hf : Q (f ∣_ U)) :
    Q (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  let V := g ⁻¹ᵁ U
  let r := pullback.snd f g
  have hb : r ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro x hx
    change g (r x) ∈ U at hx
    change f ((pullback.fst f g) x) ∈ U
    rwa [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
  let b := (pullback.fst f g).resLE (f ⁻¹ᵁ U) (r ⁻¹ᵁ V) hb
  have H : IsPullback b (r ∣_ V) (f ∣_ U) (g ∣_ U) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f U).flip
    · simpa [b] using ((isPullback_morphismRestrict r V).flip.paste_horiz
        (IsPullback.of_hasPullback f g))
    · apply (cancel_mono U.ι).mp
      simp only [Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc, pullback.condition]
      simp [r, V]
  exact MorphismProperty.of_isPullback (P := Q) H hf

private theorem punctured_stalk_mem {S : Scheme.{u}} (U : S.Opens) (s : S)
    (hs : s ∉ U) (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (x : Spec (S.presheaf.stalk s)) :
    S.fromSpecStalk s x ∈ U ↔ x ≠ IsLocalRing.closedPoint (S.presheaf.stalk s) := by
  constructor
  · intro hx he
    subst x
    rw [fromSpecStalk_closedPoint] at hx
    exact hs hx
  · intro hx
    by_contra hnot
    have hspec := (IsLocalRing.specializes_closedPoint x).map
      (S.fromSpecStalk s).continuous
    rw [fromSpecStalk_closedPoint] at hspec
    have he := hmin _ hspec hnot
    apply hx
    exact (S.fromSpecStalk s).isEmbedding.injective
      (he.trans fromSpecStalk_closedPoint.symm)

private theorem formal_test_zero_slice_mem {S C : Scheme.{u}}
    (c : C ⟶ S) (U : S.Opens) (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) (d : ℕ)
    (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶
      pullback c (S.fromSpecStalk s))
    (hb : t ≫ pullback.snd c (S.fromSpecStalk s) =
      Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d)))) :
    ∀ x : Spec (S.presheaf.stalk s),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈
        (t ≫ pullback.fst c (S.fromSpecStalk s)) ⁻¹ᵁ (c ⁻¹ᵁ U) ↔
          x ≠ IsLocalRing.closedPoint (S.presheaf.stalk s) := by
  let z := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)
    (R := S.presheaf.stalk s)))
  have hzb : z ≫ Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) = 𝟙 _ := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((MvPowerSeries.constantCoeff (σ := Fin d)).comp MvPowerSeries.C)) = _
    rw [MvPowerSeries.constantCoeff_comp_C]
    exact Spec.map_id _
  have he : (z ≫ t ≫ pullback.fst c (S.fromSpecStalk s)) ≫ c =
      S.fromSpecStalk s := by
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc t, hb, ← Category.assoc z, hzb, Category.id_comp]
  intro x
  change ((z ≫ t ≫ pullback.fst c (S.fromSpecStalk s)) ≫ c) x ∈ U ↔ _
  rw [he]
  exact punctured_stalk_mem U s hs hmin x

/-- On the original open the relative normalization is finite etale; its fixed
formal test has punctured zero slice. -/
theorem stalk_normalization_formal_punctured_restriction {S C : Scheme.{u}}
    [IsNoetherian S]
    (c : C ⟶ S)
    (G : Type (u + 1)) [Finite G]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    ∀ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      t ≫ pullback.snd c a =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) →
      let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
      let F : Scheme.{u} := pullback n t
      let E : Scheme.{u} := ∐ (fun _ : G ↦ T)
      let V := (t ≫ pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)
      let r : F ⟶ T := pullback.snd n t
      let p : E ⟶ T := Sigma.desc (fun _ : G ↦ 𝟙 T)
      IsFinite (p ∣_ V) ∧ Etale (p ∣_ V) ∧
      IsFinite (r ∣_ V) ∧ Etale (r ∣_ V) ∧
      ∀ x : Spec (S.presheaf.stalk s),
        (Spec.map (CommRingCat.ofHom
          (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
            x ≠ IsLocalRing.closedPoint (S.presheaf.stalk s) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro d t hb
  let a := S.fromSpecStalk s
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let n := pullback.snd f.fromNormalization (pullback.fst c a)
  let V := (t ≫ pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)
  have hnP (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
      [Q.IsStableUnderBaseChange] (hP : Q PA.obj.hom) :
      Q (pullback.snd n t ∣_ V) := by
    have h₁ := normalization_open_property Q (c ⁻¹ᵁ U) PA hP
    have h₂ := property_pullback_open Q f.fromNormalization (pullback.fst c a)
      (c ⁻¹ᵁ U) h₁
    have h₃ := property_pullback_open Q n t ((pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)) h₂
    simpa only [V, Hom.comp_preimage] using h₃
  have hp : IsFinite (Sigma.desc (fun _ : G ↦
      𝟙 (Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))))) := inferInstance
  have hep : Etale (Sigma.desc (fun _ : G ↦
      𝟙 (Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))))) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let := hep
  refine ⟨inferInstance, inferInstance, hnP (@IsFinite) PA.property,
    hnP (@Etale) PA.obj.prop, ?_⟩
  exact formal_test_zero_slice_mem c U s hs hmin d t hb

end AlgebraicGeometry.Scheme
