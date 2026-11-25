/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Isomorphism descent for finitely presented affine schemes

## References

* Stacks Project, Tag 05N9 (2), (3)
* Tag 0EYG, descent paragraph
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Descend all unit conditions together by factoring a one-element localization.
private theorem finite_units_stage
    (R : CommRingCat.{u})
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj R ⟶ F)
    (c : Cocone F) (hc : IsColimit c) (ι : R →+* c.pt)
    (ht : ∀ j, t.app j ≫ c.ι.app j = CommRingCat.ofHom ι)
    (m : ℕ) (a : Fin m → R) (ha : ∀ k, IsUnit (ι (a k))) :
    ∃ j, ∀ k, IsUnit ((t.app j).hom (a k)) := by
  classical
  let w : R := ∏ k, a k
  have hu : IsUnit (ι w) := by
    dsimp only [w]
    rw [map_prod]
    exact IsUnit.prod_univ_iff.mpr ha
  let B := CommRingCat.of (Localization.Away w)
  let f : R ⟶ B := CommRingCat.ofHom (algebraMap R (Localization.Away w))
  let g : B ⟶ c.pt := CommRingCat.ofHom (IsLocalization.Away.lift w hu)
  have hf : f.hom.FinitePresentation := by
    change (algebraMap R (Localization.Away w)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have hfg : f ≫ g = CommRingCat.ofHom ι := by
    exact congrArg CommRingCat.ofHom (IsLocalization.Away.lift_comp w hu)
  obtain ⟨j, g', hj, _⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R F t f c hc hf g
      (fun j ↦ hfg.trans (ht j).symm)
  have hw : IsUnit ((t.app j).hom w) := by
    have hw' : IsUnit ((f ≫ g').hom w) :=
      (IsLocalization.Away.algebraMap_isUnit w).map g'.hom
    rw [hj] at hw'
    exact hw'
  refine ⟨j, ?_⟩
  apply IsUnit.prod_univ_iff.mp
  simpa only [w, map_prod] using hw

set_option backward.defeqAttrib.useBackward true in
/-- A relative isomorphism between two fixed finitely presented affine schemes
and finitely many unit conditions descend to an etale stage of an ind-etale map. -/
theorem affine_fp_iso_descend_indEtale
    (R H : CommRingCat.{u}) (ι : R →+* H) (hι : ι.IndEtale)
    {Y Z : Scheme.{u}} (p : Y ⟶ Spec R) (q : Z ⟶ Spec R)
    (hp : IsAffineHom p ∧ LocallyOfFinitePresentation p)
    (hq : IsAffineHom q ∧ LocallyOfFinitePresentation q)
    (m : ℕ) (a : Fin m → R) (ha : ∀ k, IsUnit (ι (a k)))
    (hiso : ∃ γ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅
        pullback q (Spec.map (CommRingCat.ofHom ι)),
      γ.hom ≫ pullback.snd q (Spec.map (CommRingCat.ofHom ι)) =
        pullback.snd p (Spec.map (CommRingCat.ofHom ι))) :
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (ψ : S →+* H),
      ψ.comp φ = ι ∧ Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (∀ k, IsUnit (φ (a k))) ∧
      ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅
          pullback q (Spec.map (CommRingCat.ofHom φ)),
        γ.hom ≫ pullback.snd q (Spec.map (CommRingCat.ofHom φ)) =
          pullback.snd p (Spec.map (CommRingCat.ofHom φ))  := by
  classical
  obtain ⟨J, hcat, hfilt, F, t, c, hc, ht⟩ :=
    (RingHom.IndEtale.iff_exists (CommRingCat.ofHom ι)).mp hι
  let : SmallCategory J := hcat
  let : IsFiltered J := hfilt
  let cr : Cocone F := Cocone.mk H c
  obtain ⟨j, hj⟩ := finite_units_stage R F t cr hc ι
    (fun i ↦ (ht i).2) m a ha
  let D := F.op ⋙ Scheme.Spec
  let cs := Scheme.Spec.mapCone cr.op
  have hcs : IsLimit cs := isLimitOfPreserves Scheme.Spec hc.op
  have : ∀ i, IsAffine (D.obj i) := fun i ↦ inferInstanceAs (IsAffine (Spec (F.obj i.unop)))
  have : ∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) := fun _ ↦ inferInstance
  have : IsAffineHom p := hp.1
  have : LocallyOfFinitePresentation p := hp.2
  have : IsAffineHom q := hq.1
  have : LocallyOfFinitePresentation q := hq.2
  let b := Spec.map (CommRingCat.ofHom ι)
  let tj := Spec.map (t.app j)
  let cj := Spec.map (c.app j)
  have hcj : cj ≫ tj = b := by
    rw [← Spec.map_comp, (ht j).2]
  let pj := pullback.snd p tj
  let qj := pullback.snd q tj
  let μp := pullback.map p b p tj (𝟙 Y) cj (𝟙 _) (by simp) (by simp [hcj])
  let μq := pullback.map q b q tj (𝟙 Z) cj (𝟙 _) (by simp) (by simp [hcj])
  obtain ⟨γ, hγ⟩ := hiso
  have H₁ : IsPullback μp (pullback.snd p b) pj (cs.π.app (Opposite.op j)) :=
    isPullback_pullback_map p b tj cj hcj
  have H₂ : IsPullback (γ.hom ≫ μq) (pullback.snd p b) qj
      (cs.π.app (Opposite.op j)) := by
    exact (isPullback_pullback_map q b tj cj hcj).of_iso γ.symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by change μq = γ.inv ≫ γ.hom ≫ μq; simp)
      (by simpa using ((Iso.inv_comp_eq γ).mpr hγ.symm).symm) rfl rfl
  obtain ⟨k, f, hk⟩ := exists_iso_of_isPullback hcs H₁ H₂
  let φ := (t.app k.unop).hom
  let ψ := (c.app k.unop).hom
  let bk := Spec.map (t.app k.unop)
  let ck := Spec.map (c.app k.unop)
  have hck : ck ≫ bk = b := by
    rw [← Spec.map_comp, (ht k.unop).2]
  have hkt : D.map f ≫ tj = bk := by
    change Spec.map (F.map f.unop) ≫ Spec.map (t.app j) = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (by simpa using (t.naturality f.unop).symm)
  let νp := pullback.map p bk p tj (𝟙 Y) (D.map f) (𝟙 _)
    (by simp) (by simp [hkt])
  let νq := pullback.map q bk q tj (𝟙 Z) (D.map f) (𝟙 _)
    (by simp) (by simp [hkt])
  let lp := pullback.map p b p bk (𝟙 Y) ck (𝟙 _) (by simp) (by simp [hck])
  let lq := γ.hom ≫
    pullback.map q b q bk (𝟙 Z) ck (𝟙 _) (by simp) (by simp [hck])
  have hpstage : IsPullback νp (pullback.snd p bk) pj (D.map f) :=
    isPullback_pullback_map p bk tj (D.map f) hkt
  have hqstage : IsPullback νq (pullback.snd q bk) qj (D.map f) :=
    isPullback_pullback_map q bk tj (D.map f) hkt
  have hclegs : ck ≫ D.map f = cj := cs.w f
  have hlp : lp ≫ νp = μp := by
    apply pullback.hom_ext <;> simp [lp, νp, μp, pullback.map, Category.assoc, hclegs]
  have hlq : lq ≫ νq = γ.hom ≫ μq := by
    rw [Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [νq, μq, pullback.map, Category.assoc, hclegs]
  have hlpsnd : lp ≫ pullback.snd p bk = pullback.snd p b ≫ cs.π.app k := by
    change lp ≫ pullback.snd p bk = pullback.snd p b ≫ ck
    simp [lp, pullback.map]
  have hlqsnd : lq ≫ pullback.snd q bk = pullback.snd p b ≫ cs.π.app k := by
    change lq ≫ pullback.snd q bk = pullback.snd p b ≫ ck
    simp only [lq, Category.assoc, pullback.map, pullback.lift_snd]
    exact congrArg (fun z ↦ z ≫ ck) hγ
  obtain ⟨α, hα, _⟩ := hk hpstage hlp hlpsnd hqstage hlq hlqsnd
  refine ⟨F.obj k.unop, φ, ψ, ?_, ?_, ?_, α, hα⟩
  · exact congrArg CommRingCat.Hom.hom (ht k.unop).2
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (ht k.unop).1
  · intro l
    have hu := (hj l).map (F.map f.unop).hom
    have he : t.app j ≫ F.map f.unop = t.app k.unop := by
      simpa using (t.naturality f.unop).symm
    change IsUnit ((t.app j ≫ F.map f.unop).hom (a l)) at hu
    rw [he] at hu
    exact hu

end AlgebraicGeometry.Scheme
