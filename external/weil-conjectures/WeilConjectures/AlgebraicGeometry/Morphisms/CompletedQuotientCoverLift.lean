/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingComplete

/-! # Lifting a quotient cover before punctured comparison

## References

* Stacks Project, Tags 09ZL and 0ALJ, as used in Tag 0BLS
* Stacks Project, Tag 0BLS, complete-case lifting paragraph, using Tags 09ZL and 0ALJ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- A Cauchy sequence for J is Cauchy for m. Its m-adic limit has the right
-- residue modulo J^n because the finite module R/J^n is m-adically Hausdorff.
private theorem complete_subideal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (J : Ideal R) (hJ : J ≤ IsLocalRing.maximalIdeal R) : IsAdicComplete J R := by
  let m := IsLocalRing.maximalIdeal R
  have hpow (n : ℕ) : J ^ n • (⊤ : Submodule R R) ≤ m ^ n • ⊤ := by gcongr
  have : IsHausdorff J R := ⟨fun x hx ↦
    IsHausdorff.haus (inferInstance : IsHausdorff m R) x
      (fun n ↦ (hx n).mono (hpow n))⟩
  refine { prec' := ?_ }
  intro f hf
  obtain ⟨L, hL⟩ := IsPrecomplete.prec
    (inferInstance : IsPrecomplete m R) (f := f) (fun {a b} h ↦ (hf h).mono (hpow a))
  refine ⟨L, fun n ↦ ?_⟩
  let N : Submodule R R := J ^ n • ⊤
  have heq : N.mkQ (f n) = N.mkQ L := by
    apply (IsHausdorff.eq_iff_smodEq (I := m)).mpr
    intro k
    let l := max n k
    have hfn : N.mkQ (f n) = N.mkQ (f l) := hf (le_max_left n k)
    rw [hfn]
    have hfl : f l ≡ L [SMOD (m ^ k • (⊤ : Submodule R R))] :=
      (hL l).mono (Submodule.pow_smul_top_le m R (le_max_right n k))
    simpa only [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hfl.map N.mkQ
  exact heq

private theorem restrict_pullback_iso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (v : Z ⟶ U.toScheme) :
    ∃ e : pullback (f ∣_ U) v ≅ pullback f (v ≫ U.ι),
      e.hom ≫ pullback.snd f (v ≫ U.ι) = pullback.snd (f ∣_ U) v := by
  let H := (IsPullback.of_hasPullback (f ∣_ U) v).paste_horiz
    (isPullback_morphismRestrict f U).flip
  exact ⟨H.isoPullback, H.isoPullback_hom_snd⟩

private theorem base_change_iso
    {X Y Z S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (e : X ≅ Y) (he : e.hom ≫ g = f) (v : Z ⟶ S) :
    ∃ a : pullback f v ≅ pullback g v,
      a.hom ≫ pullback.snd g v = pullback.snd f v := by
  let a := asIso (pullback.map f v g v e.hom (𝟙 _) (𝟙 _)
    (by simpa using he.symm) (by simp))
  exact ⟨a, by simp [a]⟩

/-- A finite etale quotient extension gives a completed cover agreeing on the quotient. -/
theorem exists_completed_cover_with_quotient_iso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (U : (Spec (.of A)).Opens)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q]
    (hquot :
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let V := i ⁻¹ᵁ U
      ∃ (F₀ : Scheme.{u}) (r₀ : F₀ ⟶ Spec (.of (A ⧸ Ideal.span {f}))),
        IsFinite r₀ ∧ Etale r₀ ∧
          ∃ e₀ : pullback q (i ∣_ U) ≅ (r₀ ⁻¹ᵁ V).toScheme,
            e₀.hom ≫ r₀ ∣_ V = pullback.snd q (i ∣_ U)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let W := c ⁻¹ᵁ U
    let j := Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {algebraMap A C f})))
    ∃ (E : Scheme.{u}) (s : E ⟶ Spec (.of C)), IsFinite s ∧ Etale s ∧
      ∃ e₀ : pullback (pullback.snd q (c ∣_ U)) (j ∣_ W) ≅
          pullback (s ∣_ W) (j ∣_ W),
        e₀.hom ≫ pullback.snd (s ∣_ W) (j ∣_ W) =
          pullback.snd (pullback.snd q (c ∣_ U)) (j ∣_ W) := by
  classical
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let J : Ideal C := Ideal.span {algebraMap A C f}
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  let W := c ⁻¹ᵁ U
  let V := i ⁻¹ᵁ U
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing _
  have hJ : J ≤ IsLocalRing.maximalIdeal C := by
    apply Ideal.span_le.mpr
    rintro x (rfl : x = algebraMap A C f)
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ hf
  have : IsAdicComplete J C := complete_subideal C J hJ
  have hmap : Ideal.span {f} ≤ J.comap (algebraMap A C) := by
    apply Ideal.span_le.mpr
    rintro x (rfl : x = f)
    exact Ideal.subset_span (by simp)
  let k := Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A C) hmap))
  have hcomm : j ≫ c = k ≫ i := by
    dsimp [j, c, k, i]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  obtain ⟨F₀, r₀, hrfin, hret, e₀, he₀⟩ := hquot
  have : IsFinite r₀ := hrfin
  have : Etale r₀ := hret
  let r := pullback.snd r₀ k
  let hbase := IsPullback.id_vert j
  let ebase := hbase.isoPullback
  let p := pullback.fst (𝟙 (Spec (.of C))) j
  let T : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback (𝟙 (Spec (.of C))) j) :=
    MorphismProperty.Over.mk ⊤ (r ≫ ebase.hom) ⟨inferInstance, inferInstance⟩
  -- Apply only the complete-base lifting input, with the proper identity as base.
  obtain ⟨S, ⟨a⟩⟩ := exists_finiteEtale_lift_of_isAdicComplete J (𝟙 (Spec (.of C))) T
  let s := S.hom
  have : IsFinite s := S.prop.1
  have : Etale s := S.prop.2
  have hbasep : ebase.hom ≫ p = j := hbase.isoPullback_hom_fst
  let bbase : pullback s j ≅ pullback s p := asIso
    (pullback.map s j s p (𝟙 _) ebase.hom (𝟙 _)
      (by simp) (by simpa using hbasep.symm))
  let eg : pullback s j ≅ pullback r₀ k := bbase ≪≫ (Over.forget _).mapIso a
  have heg : eg.hom ≫ pullback.snd r₀ k = pullback.snd s j := by
    apply (cancel_mono ebase.hom).mp
    have ha : a.hom.left ≫ r ≫ ebase.hom = pullback.snd s p := a.hom.w
    change (bbase.hom ≫ a.hom.left) ≫ r ≫ ebase.hom = _
    simp only [Category.assoc, ha]
    simp [bbase]
  let W₀ := j ⁻¹ᵁ W
  have hj : j ∣_ W ≫ W.ι = W₀.ι ≫ j := morphismRestrict_ι j W
  have hopen : W₀ = k ⁻¹ᵁ V := by
    change (j ≫ c) ⁻¹ᵁ U = (k ≫ i) ⁻¹ᵁ U
    rw [hcomm]
  let v : W₀.toScheme ⟶ V.toScheme :=
    ((Spec (.of (C ⧸ J))).isoOfEq hopen).hom ≫ k ∣_ V
  have hv : v ≫ V.ι = W₀.ι ≫ k := by
    dsimp [v]
    simp only [Category.assoc, morphismRestrict_ι, isoOfEq_hom_ι_assoc]
  have hres : j ∣_ W ≫ c ∣_ U = v ≫ i ∣_ U := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, morphismRestrict_ι]
    change j ∣_ W ≫ W.ι ≫ c = v ≫ V.ι ≫ i
    rw [morphismRestrict_ι_assoc, hcomm, ← reassoc_of% hv]
  change e₀.hom ≫ r₀ ∣_ V = pullback.snd q (i ∣_ U) at he₀
  obtain ⟨b, hb⟩ := base_change_iso e₀ he₀ v
  obtain ⟨d, hd⟩ := restrict_pullback_iso r₀ V v
  have heginv : eg.symm.hom ≫ pullback.snd s j = pullback.snd r₀ k :=
    (Iso.inv_comp_eq eg).mpr heg.symm
  obtain ⟨e, he⟩ := base_change_iso eg.symm heginv W₀.ι
  obtain ⟨t, ht⟩ := restrict_pullback_iso s W (j ∣_ W)
  let z := pullbackLeftPullbackSndIso q (c ∣_ U) (j ∣_ W) ≪≫
    pullback.congrHom rfl hres ≪≫
    (pullbackLeftPullbackSndIso q (i ∣_ U) v).symm ≪≫ b ≪≫ d ≪≫
    pullback.congrHom rfl hv ≪≫
    (pullbackLeftPullbackSndIso r₀ k W₀.ι).symm ≪≫ e ≪≫
    pullbackLeftPullbackSndIso s j W₀.ι ≪≫
    pullback.congrHom rfl hj.symm ≪≫ t.symm
  refine ⟨S.left, s, inferInstance, inferInstance, z, ?_⟩
  have ht' : t.inv ≫ pullback.snd (s ∣_ W) (j ∣_ W) =
      pullback.snd s (j ∣_ W ≫ W.ι) := (Iso.inv_comp_eq t).mpr ht.symm
  change z.hom ≫ pullback.snd (s ∣_ W) (j ∣_ W) =
    pullback.snd (pullback.snd q (c ∣_ U)) (j ∣_ W)
  simp only [z, Iso.trans_hom, Iso.symm_hom, Category.assoc, ht',
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd, pullbackLeftPullbackSndIso_inv_snd_snd,
    he, hd, hb]

end AlgebraicGeometry.Scheme
