/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Principal-open base change of the punctured matching comparison

## References

* Stacks Project, Tags 0BLH and 05ER, localized comparison paragraph
* Stacks Project, Tag 05ER, second paragraph, applied to the overlap identification of Tag 0BLH
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
variable {E : Scheme.{u}} {s : E ⟶ Spec
  (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
variable (D : CompletionGluingData A U q E s)

set_option backward.isDefEq.respectTransparency false in
private theorem overlap_fromPunctured :
    pullback.fst q (completionSpecMap A ∣_ U) ≫ D.fromPunctured =
      D.toCompleted ≫ D.fromCompleted := by
  dsimp only [fromPunctured, fromCompleted, model, matchingRing]
  rw [toSpecΓ_naturality_assoc, toSpecΓ_naturality_assoc,
    ← Spec.map_comp, ← Spec.map_comp, pullback.condition]

private theorem overlap_pullback [IsIso D.puncturedMap] :
    IsPullback
      (D.overlapIso.inv ≫ pullback.fst q (completionSpecMap A ∣_ U) ≫ D.puncturedMap)
      (s ∣_ (completionSpecMap A ⁻¹ᵁ U))
      (D.modelMap ∣_ U) (completionSpecMap A ∣_ U) := by
  apply (IsPullback.of_hasPullback q (completionSpecMap A ∣_ U)).of_iso
    D.overlapIso (asIso D.puncturedMap) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa using D.over.symm
  · simpa using D.puncturedMap_over.symm
  · simp

set_option backward.isDefEq.respectTransparency false in
private theorem puncture_pullback [IsIso D.puncturedMap] :
    IsPullback
      ((s ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)).ι ≫ D.fromCompleted)
      (s ∣_ (completionSpecMap A ⁻¹ᵁ U))
      D.modelMap
      ((completionSpecMap A ⁻¹ᵁ U).ι ≫ completionSpecMap A) := by
  have H := (overlap_pullback D).paste_horiz (isPullback_morphismRestrict D.modelMap U).flip
  convert H using 1
  · simp only [Category.assoc, puncturedMap, pullbackRestrictIsoRestrict_hom_ι,
      pullback.lift_fst]
    simp [Category.assoc, overlap_fromPunctured, toCompleted]
  · rw [morphismRestrict_ι]

set_option backward.isDefEq.respectTransparency false in
private theorem affineCompletedMap_fst :
    (E.toSpecΓ ≫ Spec.map D.completedRingMap) ≫ Spec.map (pushout.inl D.baseMap
      (CommRingCat.ofHom (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) =
      D.fromCompleted := by
  rw [Category.assoc, ← Spec.map_comp]
  simp only [completedRingMap, pushout.inl_desc, fromCompleted]

set_option backward.isDefEq.respectTransparency false in
private theorem affineCompletedMap_snd :
    (E.toSpecΓ ≫ Spec.map D.completedRingMap) ≫ Spec.map (pushout.inr D.baseMap
      (CommRingCat.ofHom (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) =
      s := by
  rw [Category.assoc, ← Spec.map_comp]
  simp only [completedRingMap, pushout.inr_desc]
  rw [Spec.map_comp, ← Category.assoc, ← toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem affineCompletedMap_puncture_isIso [IsIso D.puncturedMap] :
    IsIso ((E.toSpecΓ ≫ Spec.map D.completedRingMap) ∣_
      ((Spec.map (pushout.inr D.baseMap (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))) ⁻¹ᵁ
          (completionSpecMap A ⁻¹ᵁ U))) := by
  let k := E.toSpecΓ ≫ Spec.map D.completedRingMap
  let p := Spec.map (pushout.inr D.baseMap (CommRingCat.ofHom
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
  let C_U := completionSpecMap A ⁻¹ᵁ U
  let W := p ⁻¹ᵁ C_U
  let V := s ⁻¹ᵁ C_U
  have hkp : k ≫ p = s := affineCompletedMap_snd D
  have hV : V = k ⁻¹ᵁ W := by
    change s ⁻¹ᵁ C_U = k ⁻¹ᵁ (p ⁻¹ᵁ C_U)
    calc
      _ = (k ≫ p) ⁻¹ᵁ C_U := congrArg (fun g ↦ g ⁻¹ᵁ C_U) hkp.symm
      _ = _ := Hom.comp_preimage k p C_U
  let e : V ≤ k ⁻¹ᵁ W := hV.le
  let H := isPullback_SpecMap_pushout D.baseMap (CommRingCat.ofHom
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
  have HT := (isPullback_morphismRestrict p C_U).flip.paste_horiz H
  have Hleft : IsPullback (k.resLE W V e) (s ∣_ C_U) (p ∣_ C_U) (𝟙 _) := by
    apply IsPullback.of_right (t := HT)
    · change IsPullback
        ((k.resLE W V e ≫ W.ι) ≫ Spec.map (pushout.inl D.baseMap _))
        (s ∣_ C_U) D.modelMap (C_U.ι ≫ completionSpecMap A)
      rw [Hom.resLE_comp_ι, Category.assoc]
      change IsPullback (V.ι ≫ ((E.toSpecΓ ≫ Spec.map D.completedRingMap) ≫
        Spec.map (pushout.inl D.baseMap _))) _ _ _
      rw [affineCompletedMap_fst]
      exact puncture_pullback D
    · rw [← cancel_mono C_U.ι]
      simp only [Category.assoc, morphismRestrict_ι, Category.id_comp]
      change k.resLE W V e ≫ W.ι ≫ p = V.ι ≫ s
      rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc, hkp]
  have hkres : IsIso (k.resLE W V e) := Hleft.isIso_fst_of_isIso
  have hi : IsIso (E.homOfLE e) := by
    exact (inferInstance : IsIso (E.isoOfEq hV).hom)
  change IsIso (k ∣_ W)
  have : IsIso (E.homOfLE e ≫ k ∣_ W) := hkres
  exact IsIso.of_isIso_comp_left (E.homOfLE e) (k ∣_ W)

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_restrict_of_le {X Z : Scheme.{u}} (k : X ⟶ Z)
    {W V : Z.Opens} [IsIso (k ∣_ W)] (h : V ≤ W) : IsIso (k ∣_ V) := by
  let O := W.ι ⁻¹ᵁ V
  have hO : W.ι ''ᵁ O = V := by
    dsimp [O]
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.mpr h]
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict k W O ≪≫ morphismRestrictEq k hO)).mp
      (inferInstanceAs (IsIso ((k ∣_ W) ∣_ O)))

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism on the punctured model gives an isomorphism of the completed
comparison after localization at any principal open contained in the puncture. -/
theorem completedRingMap_away_bijective_of_puncturedMap_isIso
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) [IsIso D.puncturedMap]
    (f : A) (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    Function.Bijective (Localization.awayMap D.completedRingMap.hom
      ((D.baseMap ≫ pushout.inl _ _).hom f)) := by
  have : IsAffine E := isAffine_of_isAffineHom s
  let ψ := Spec.map D.completedRingMap
  let p := Spec.map (pushout.inr D.baseMap (CommRingCat.ofHom
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
  let W := p ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)
  have hk : IsIso ((E.toSpecΓ ≫ ψ) ∣_ W) := affineCompletedMap_puncture_isIso D
  rw [morphismRestrict_comp] at hk
  have : IsIso (ψ ∣_ W) :=
    IsIso.of_isIso_comp_left (E.toSpecΓ ∣_ ψ ⁻¹ᵁ W) (ψ ∣_ W)
  have hbasic : (PrimeSpectrum.basicOpen ((D.baseMap ≫ pushout.inl _ _).hom f) :
      (Spec (pushout D.baseMap (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).Opens) ≤ W := by
    change _ ≤ p ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)
    rw [← Hom.comp_preimage]
    change _ ≤ (Spec.map (pushout.inr D.baseMap _) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A
        (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) ⁻¹ᵁ U
    rw [← Spec.map_comp, ← pushout.condition]
    rw [← PrimeSpectrum.comap_basicOpen (D.baseMap ≫ pushout.inl _ _).hom f]
    exact (Spec.map (D.baseMap ≫ pushout.inl _ _)).preimage_mono hf
  have : IsIso (ψ ∣_ PrimeSpectrum.basicOpen ((D.baseMap ≫ pushout.inl _ _).hom f)) :=
    isIso_restrict_of_le ψ hbasic
  apply (isIso_SpecMap_iff (f := CommRingCat.ofHom
    (Localization.awayMap D.completedRingMap.hom
      ((D.baseMap ≫ pushout.inl _ _).hom f)))).mp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (SpecMapRestrictBasicOpenIso D.completedRingMap
      ((D.baseMap ≫ pushout.inl _ _).hom f))).mp inferInstance

end AlgebraicGeometry.Scheme.CompletionGluingData
