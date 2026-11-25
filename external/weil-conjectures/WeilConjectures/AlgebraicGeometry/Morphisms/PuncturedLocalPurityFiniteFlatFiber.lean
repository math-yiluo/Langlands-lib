/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatQuasiFiniteDepthPurity
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore


/-!
# Local purity excludes a minimal nonflat fibre

## References

* Stacks Project, Tags 0BMA, 0EY7 and 0EY6(2), (3)
* Stacks Project, Tag 0EY7, the punctured local-spectrum step, and Tag 0EY6(2), (3)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem etale_restrict_of_pullback {E L T P : Scheme.{u}}
    (p : E ⟶ L) (t : T ⟶ L) (f : P ⟶ E) (q : P ⟶ T)
    (H : IsPullback f q p t) (V : L.Opens) [Etale (p ∣_ V)] :
    Etale (q ∣_ (t ⁻¹ᵁ V)) := by
  have heq : f ⁻¹ᵁ (p ⁻¹ᵁ V) = q ⁻¹ᵁ (t ⁻¹ᵁ V) := by
    simp only [← Hom.comp_preimage, H.w]
  have H' := Hom.isPullback_resLE H
    (US := V) (UT := t ⁻¹ᵁ V) (UX := p ⁻¹ᵁ V) le_rfl le_rfl
    (UY := q ⁻¹ᵁ (t ⁻¹ᵁ V)) (by rw [heq, inf_idem])
  simpa only [Hom.resLE_eq_morphismRestrict] using
    (MorphismProperty.of_isPullback (P := @Etale) H' (by
      simpa only [Hom.resLE_eq_morphismRestrict] using (inferInstance : Etale (p ∣_ V))))

private theorem punctured_stalk_etale {L E : Scheme.{u}} [IsLocallyNoetherian L]
    (V : L.Opens) (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)]
    (hsource : ∀ z : E, p z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (s : L) (U : (Spec (L.presheaf.stalk s)).Opens)
    (hU : ∀ x : Spec (L.presheaf.stalk s),
      x ∈ U ↔ x ≠ IsLocalRing.closedPoint (L.presheaf.stalk s))
    (hflat : ∀ t : L, t ⤳ s → t ≠ s →
      ∀ z : E, p z = t → (p.stalkMap z).hom.Flat) :
    Etale ((pullback.snd p (L.fromSpecStalk s)) ∣_ U) := by
  classical
  let a := L.fromSpecStalk s
  let n := pullback.snd p a
  let f := pullback.fst p a
  let W : L.Opens := ⟨{y | ∀ x : E, p x = y → (p.stalkMap x).hom.Flat},
    isOpen_setOf_finite_flat_stalks p⟩
  have : Flat (p ∣_ W) := by
    apply Flat.of_stalkMap
    intro z
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p W z)).mpr (z.2 z.1 rfl)
  have hUW : U ≤ a ⁻¹ᵁ W := by
    intro x hx
    have hxs : a x ⤳ s := by
      exact ((IsLocalRing.specializes_closedPoint x).map a.continuous).trans
        (specializes_of_eq L.fromSpecStalk_closedPoint)
    have hne : a x ≠ s := by
      intro he
      apply (hU x).mp hx
      apply a.isEmbedding.injective
      exact he.trans L.fromSpecStalk_closedPoint.symm
    exact hflat (a x) hxs hne
  have heq : f ⁻¹ᵁ (p ⁻¹ᵁ W) = n ⁻¹ᵁ (a ⁻¹ᵁ W) := by
    simp only [f, n, ← Hom.comp_preimage, pullback.condition]
  have H := Hom.isPullback_resLE (IsPullback.of_hasPullback p a)
    (US := W) (UT := U) (UX := p ⁻¹ᵁ W) hUW le_rfl
    (UY := n ⁻¹ᵁ U) (by rw [heq, inf_eq_right.mpr (n.preimage_mono hUW)])
  have : Flat (n ∣_ U) := by
    simpa only [n, Hom.resLE_eq_morphismRestrict] using
      (MorphismProperty.of_isPullback (P := @Flat) H (by
        simpa only [Hom.resLE_eq_morphismRestrict] using (inferInstance : Flat (p ∣_ W))))
  have : Etale (n ∣_ (a ⁻¹ᵁ V)) :=
    etale_restrict_of_pullback p a f n (IsPullback.of_hasPullback p a) V
  let q := n ∣_ U
  let T : U.toScheme.Opens := U.ι ⁻¹ᵁ (a ⁻¹ᵁ V)
  have : Etale (q ∣_ T) :=
    etale_restrict_of_pullback n U.ι (n ⁻¹ᵁ U).ι q (isPullback_morphismRestrict n U).flip
      (a ⁻¹ᵁ V)
  have het : Etale ((q ⁻¹ᵁ T).ι ≫ q) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian (pullback p a) := LocallyOfFiniteType.isLocallyNoetherian n
  have hdepth : ∀ w : (n ⁻¹ᵁ U).toScheme, q w ∉ T →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (n ⁻¹ᵁ U).toScheme.presheaf.stalk w) ((n ⁻¹ᵁ U).toScheme.presheaf.stalk w) := by
    intro w hw
    let g := (n ⁻¹ᵁ U).ι ≫ f
    have hgp : g ≫ p = q ≫ U.ι ≫ a := by
      dsimp [g, f, q, n]
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← morphismRestrict_ι,
        Category.assoc]
    have hw' : p (g w) ∉ V := by
      change a (U.ι (q w)) ∉ V at hw
      have hc : p (g w) = a (U.ι (q w)) := by
        rw [← Hom.comp_apply, hgp]
        simp only [Hom.comp_apply]
      rw [hc]
      exact hw
    obtain ⟨_, hlocal, _, hd⟩ :=
      IsLocalRing.depth_eq_add_of_flat_local (g.stalkMap w).hom (Flat.stalkMap g w)
    rw [hd]
    exact (hsource (g w) hw').trans le_self_add
  exact etale_of_flat_quasiFinite_depth_two_boundary q (q ⁻¹ᵁ T) het hdepth

/-- A finite depth-two extension is flat over s if it is flat over every proper
 generalization of s and purity holds for the punctured local spectrum at s. -/
theorem flat_fibre_of_punctured_local_purity
    {L E : Scheme.{u}} [IsLocallyNoetherian L] (V : L.Opens)
    (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)]
    (hsource : ∀ z : E, p z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (s : L) (hs : s ∉ V)
    (hdepth : (2 : ℕ∞) ≤
      IsLocalRing.depth (R := L.presheaf.stalk s) (L.presheaf.stalk s))
    (hpurity : ∀ (U : (Spec (L.presheaf.stalk s)).Opens),
        (∀ x : Spec (L.presheaf.stalk s),
          x ∈ U ↔ x ≠ IsLocalRing.closedPoint (L.presheaf.stalk s)) →
        ∀ (Z : Scheme.{u}) (q : Z ⟶ U.toScheme), IsFinite q → Etale q →
          ∃ (F : Scheme.{u}) (r : F ⟶ Spec (L.presheaf.stalk s)),
            IsFinite r ∧ Etale r ∧
              ∃ e : Z ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q)
    (hflat : ∀ t : L, t ⤳ s → t ≠ s →
      ∀ z : E, p z = t → (p.stalkMap z).hom.Flat) :
    ∀ z : E, p z = s → (p.stalkMap z).hom.Flat := by
  classical
  let A := L.presheaf.stalk s
  let a := L.fromSpecStalk s
  let n := pullback.snd p a
  let f := pullback.fst p a
  let U : (Spec A).Opens :=
    ⟨{IsLocalRing.closedPoint A}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint A).isOpen_compl⟩
  have hU : ∀ x : Spec A, x ∈ U ↔ x ≠ IsLocalRing.closedPoint A := by
    intro x
    simp [U]
  have : Etale (n ∣_ U) := punctured_stalk_etale V p hsource s U hU hflat
  have : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian (pullback p a) := LocallyOfFiniteType.isLocallyNoetherian n
  have hn : ∀ w : ↥(pullback p a), n w ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := (pullback p a).presheaf.stalk w)
        ((pullback p a).presheaf.stalk w) := by
    intro w hw
    have hclosed : n w = IsLocalRing.closedPoint A := by
      by_contra hne
      exact hw ((hU (n w)).mpr hne)
    have hw' : p (f w) = s := by
      calc
        p (f w) = a (n w) := by
          rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
        _ = s := by rw [hclosed]; exact L.fromSpecStalk_closedPoint
    obtain ⟨_, hlocal, _, hd⟩ :=
      IsLocalRing.depth_eq_add_of_flat_local (f.stalkMap w).hom (Flat.stalkMap f w)
    rw [hd]
    exact (hsource (f w) (by rw [hw']; exact hs)).trans le_self_add
  have hA : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := (Spec A).presheaf.stalk (IsLocalRing.closedPoint A))
      ((Spec A).presheaf.stalk (IsLocalRing.closedPoint A)) := by
    let e := stalkClosedPointIso A
    let φ := e.inv.hom
    have hbij : Function.Bijective φ := ConcreteCategory.bijective_of_isIso e.inv
    let : IsLocalHom φ := IsLocalHom.of_surjective φ hbij.2
    obtain ⟨_, hlocal, _, hd⟩ :=
      IsLocalRing.depth_eq_add_of_flat_local φ (RingHom.Flat.of_bijective hbij)
    rw [hd]
    exact hdepth.trans le_self_add
  obtain ⟨F, r, hfin, het, e, he⟩ :=
    hpurity U hU (n ⁻¹ᵁ U).toScheme (n ∣_ U) inferInstance inferInstance
  let := hfin
  let := het
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian r
  have hr : ∀ w : F, r w ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk w) (F.presheaf.stalk w) := by
    intro w hw
    have hclosed : r w = IsLocalRing.closedPoint A := by
      by_contra hne
      exact hw ((hU (r w)).mpr hne)
    obtain ⟨_, hlocal, _, hd⟩ :=
      IsLocalRing.depth_eq_add_of_flat_local (r.stalkMap w).hom (Flat.stalkMap r w)
    rw [hd]
    exact (hclosed ▸ hA).trans le_self_add
  obtain ⟨i, hi⟩ := iso_of_finite_depth_two_extensions U r n hr hn e he
  have hn' : n = i.inv ≫ r := by
    rw [← hi, ← Category.assoc, i.inv_hom_id, Category.id_comp]
  have : Flat n := by
    rw [hn']
    infer_instance
  obtain ⟨W, hsW, hW⟩ := stalk_normalization_depth_two_section_flat_core p a s
    (IsLocalRing.closedPoint A) L.fromSpecStalk_closedPoint
  let := hW
  intro z hz
  let zW : (p ⁻¹ᵁ W).toScheme := ⟨z, by change p z ∈ W; rwa [hz]⟩
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap p W zW)).mp (Flat.stalkMap (p ∣_ W) zW)


end AlgebraicGeometry.Scheme
