/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.FirstOrderThickeningBaseChange
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces

/-! # Triple-overlap cocycle for universal thickenings

Source: Stacks Project, More on Morphisms, Tag 04F3, proof of Lemma 37.7.1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Canonical transitions of universal overlap restrictions extend to triple overlaps
and satisfy the cocycle, without asserting the existence of a scheme glue datum.

Source: Stacks Project, More on Morphisms, Tag 04F3, proof of Lemma 37.7.1,
paragraph beginning "By the general remarks".
(blueprint: lem-weil-pbc-universal-thickening-overlap-cocycle)

Proof: The existing open-pieces theorem gives unique inverse-image opens for
each s(k,l). Its closed image has open complement with empty preimage, so
uniqueness identifies that complement with the empty open. Thus every point
lifts along s(k,l).
The transition fixes the source intersection, identified by pullback symmetry.
The pointwise range equivalence therefore shows that t(k,l) carries the open
triple intersection in V(k,l) into the triple intersection in V(l,k). Factor
this restriction through the open immersion V(l,m) into Z' l and use the
pullback universal property to construct t'(k,l,m). Its second projection is
by construction the first projection followed by t(k,l). To check the cocycle, pull back s(k,l)
along the first projection of the triple
overlap P=V(k,l) ×[Z' k] V(k,m). This gives a first order test thickening j:Q→P
by the base-change theorem. Its map to the source pair supplies the k and l
coordinates. The range equivalence for f(k,m) shows that its k coordinate maps
into the image of C.f m, so the open-immersion lifting property supplies the m
coordinate. Form the source pairs (l,m) and (m,k) using these coordinates.
After composing with f(l,m), the first projection of j followed by t'(k,l,m)
is the l coordinate followed by i l; cancel this open immersion to identify the
projection with the source pair followed by s(l,m). Repeat this argument twice.
The full cyclic composite therefore extends the same source map as P's first
projection. Each t' is over X by its second-projection identity and base
compatibility of t. The lifting uniqueness for s(k,l), applied to j, identifies
the cyclic composite followed by P's first projection with that projection.
The projection is a monomorphism, so the cyclic composite is the identity.
Repeated indices use the same argument; no inequality assumptions are needed.
Empty index types give vacuous conditions. -/
theorem universalFirstOrderThickening_overlapCocycle
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (V : C.I₀ × C.I₀ → Scheme.{u}) (f : ∀ k l, V (k, l) ⟶ Z' k)
    (s : ∀ k l, pullback (C.f k) (C.f l) ⟶ V (k, l))
    (hf : ∀ k l, IsOpenImmersion (f k l))
    (Hs : ∀ k l, IsUniversalFirstOrderThickening
      (pullback.fst (C.f k) (C.f l) ≫ C.f k ≫ h) (s k l) (f k l ≫ h' k))
    (hsf : ∀ k l, s k l ≫ f k l = pullback.fst _ _ ≫ i k)
    (hrange : ∀ k l (z : C.X k),
      i k z ∈ Set.range (f k l) ↔ C.f k z ∈ Set.range (C.f l))
    (t : ∀ k l, V (k, l) ⟶ V (l, k))
    (htbase : ∀ k l, t k l ≫ f l k ≫ h' l = f k l ≫ h' k)
    (htsource : ∀ k l,
      s k l ≫ t k l = (pullbackSymmetry (C.f k) (C.f l)).hom ≫ s l k) :
    ∃ t' : ∀ k l m, pullback (f k l) (f k m) ⟶ pullback (f l m) (f l k),
      (∀ k l m, t' k l m ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t k l) ∧
      ∀ k l m, t' k l m ≫ t' l m k ≫ t' m k l = 𝟙 _ := by
  classical
  have (k l : C.I₀) : IsOpenImmersion (f k l) := hf k l
  have ht_sf (k l : C.I₀) :
      s k l ≫ t k l ≫ f l k = pullback.snd (C.f k) (C.f l) ≫ i l := by
    rw [← Category.assoc, htsource, Category.assoc, hsf]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
  have triple_range (k l m : C.I₀) :
      Set.range (pullback.fst (f k l) (f k m) ≫ t k l ≫ f l k) ⊆
        Set.range (f l m) := by
    rintro _ ⟨p, rfl⟩
    have : IsClosedImmersion (s k l) := (Hs k l).1.1
    let W : (V (k, l)).Opens :=
      ⟨(Set.range (s k l))ᶜ, (s k l).isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hW : s k l ⁻¹ᵁ W = ⊥ := by
      ext x
      simp [W]
    have hbot : s k l ⁻¹ᵁ (⊥ : (V (k, l)).Opens) = ⊥ := by
      ext x
      simp
    have huniq := ((universalFirstOrderThickening_open_pieces h).1
      (s k l) (f k l ≫ h' k) (Hs k l).1).2
      (⊥ : (pullback (C.f k) (C.f l)).Opens)
    have hWbot : W = ⊥ := huniq.unique hW hbot
    obtain ⟨x, hx⟩ : ∃ x, s k l x = pullback.fst (f k l) (f k m) p := by
      by_contra hn
      have hp : pullback.fst (f k l) (f k m) p ∈ W := hn
      rw [hWbot] at hp
      exact hp
    have hxk : i k (pullback.fst (C.f k) (C.f l) x) =
        f k m (pullback.snd (f k l) (f k m) p) := by
      have hsx := congrArg (fun q ↦ q x) (hsf k l)
      have hp := congrArg (fun q ↦ q p) (pullback.condition (f := f k l) (g := f k m))
      simp only [Scheme.Hom.comp_apply] at hsx hp
      rw [← hsx, hx, hp]
    have hxm : C.f k (pullback.fst (C.f k) (C.f l) x) ∈ Set.range (C.f m) :=
      (hrange k m _).mp ⟨_, hxk.symm⟩
    have hxl : C.f l (pullback.snd (C.f k) (C.f l) x) ∈ Set.range (C.f m) := by
      have hc := congrArg (fun q ↦ q x)
        (pullback.condition (f := C.f k) (g := C.f l))
      simp only [Scheme.Hom.comp_apply] at hc
      rw [← hc]
      exact hxm
    have htx := congrArg (fun q ↦ q x) (ht_sf k l)
    simp only [Scheme.Hom.comp_apply] at htx
    simp only [Scheme.Hom.comp_apply]
    rw [← hx, htx]
    exact (hrange l m _).mpr hxl
  let t' (k l m : C.I₀) :
      pullback (f k l) (f k m) ⟶ pullback (f l m) (f l k) :=
    pullback.lift
      (IsOpenImmersion.lift (f l m)
        (pullback.fst (f k l) (f k m) ≫ t k l ≫ f l k) (triple_range k l m))
      (pullback.fst (f k l) (f k m) ≫ t k l)
      (IsOpenImmersion.lift_fac _ _ _)
  have ht_fac (k l m : C.I₀) :
      t' k l m ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t k l :=
    pullback.lift_snd _ _ _
  have ht_base (k l m : C.I₀) :
      t' k l m ≫ pullback.fst _ _ ≫ f l m ≫ h' l =
        pullback.fst _ _ ≫ f k l ≫ h' k := by
    calc
      _ = t' k l m ≫ pullback.snd _ _ ≫ f l k ≫ h' l := by
        simpa only [Category.assoc] using congrArg (fun q ↦ t' k l m ≫ q ≫ h' l)
          (pullback.condition (f := f l m) (g := f l k))
      _ = pullback.fst _ _ ≫ t k l ≫ f l k ≫ h' l := by
        simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ f l k ≫ h' l)
          (ht_fac k l m)
      _ = _ := by rw [htbase]
  have next_source {S : Scheme.{u}} (k l m : C.I₀)
      (q : S ⟶ pullback (f k l) (f k m))
      (a : S ⟶ pullback (C.f k) (C.f l))
      (b : S ⟶ pullback (C.f l) (C.f m))
      (hq : q ≫ pullback.fst _ _ = a ≫ s k l)
      (hab : a ≫ pullback.snd _ _ = b ≫ pullback.fst _ _) :
      q ≫ t' k l m ≫ pullback.fst _ _ = b ≫ s l m := by
    apply (cancel_mono (f l m)).mp
    calc
      _ = q ≫ t' k l m ≫ pullback.snd _ _ ≫ f l k := by
        simpa only [Category.assoc] using congrArg (fun r ↦ q ≫ t' k l m ≫ r)
          (pullback.condition (f := f l m) (g := f l k))
      _ = (q ≫ pullback.fst _ _) ≫ t k l ≫ f l k := by
        simpa only [Category.assoc] using congrArg (fun r ↦ q ≫ r ≫ f l k)
          (ht_fac k l m)
      _ = (a ≫ s k l) ≫ t k l ≫ f l k := by rw [hq]
      _ = (a ≫ pullback.snd _ _) ≫ i l := by
        simpa only [Category.assoc] using congrArg (fun r ↦ a ≫ r) (ht_sf k l)
      _ = (b ≫ pullback.fst _ _) ≫ i l := by rw [hab]
      _ = _ := by rw [Category.assoc, Category.assoc, hsf]
  refine ⟨t', ht_fac, ?_⟩
  intro k l m
  let p := pullback.fst (f k l) (f k m)
  let j := pullback.fst p (s k l)
  let a := pullback.snd p (s k l)
  have hj : IsFirstOrderThickening j :=
    (IsFirstOrderThickening.baseChange (s k l) p (Hs k l).1).1
  have hja : j ≫ p = a ≫ s k l := pullback.condition
  let zk := a ≫ pullback.fst (C.f k) (C.f l)
  let zl := a ≫ pullback.snd (C.f k) (C.f l)
  have hzk : zk ≫ i k = j ≫ pullback.snd (f k l) (f k m) ≫ f k m := by
    calc
      _ = a ≫ s k l ≫ f k l := by
        dsimp only [zk]
        rw [Category.assoc, hsf]
      _ = j ≫ p ≫ f k l := by rw [← Category.assoc, ← hja, Category.assoc]
      _ = _ := by
        exact congrArg (fun q ↦ j ≫ q) (pullback.condition (f := f k l) (g := f k m))
  have hmrange : Set.range (zk ≫ C.f k) ⊆ Set.range (C.f m) := by
    rintro _ ⟨q, rfl⟩
    have heq := congrArg (fun r ↦ r q) hzk
    simp only [Scheme.Hom.comp_apply] at heq ⊢
    exact (hrange k m (zk q)).mp ⟨_, heq.symm⟩
  let zm := IsOpenImmersion.lift (C.f m) (zk ≫ C.f k) hmrange
  have hzm : zm ≫ C.f m = zk ≫ C.f k := IsOpenImmersion.lift_fac _ _ _
  have hzl : zl ≫ C.f l = zk ≫ C.f k := by
    dsimp only [zl, zk]
    rw [Category.assoc, Category.assoc, pullback.condition]
  let alm := pullback.lift zl zm (hzl.trans hzm.symm)
  let amk := pullback.lift zm zk hzm
  have h1 : (j ≫ t' k l m) ≫ pullback.fst _ _ = alm ≫ s l m := by
    apply next_source k l m j a alm hja
    simp only [alm, pullback.lift_fst]
    rfl
  have h2 : (j ≫ t' k l m ≫ t' l m k) ≫ pullback.fst _ _ = amk ≫ s m k := by
    apply next_source l m k (j ≫ t' k l m) alm amk h1
    simp only [alm, amk, pullback.lift_snd, pullback.lift_fst]
  have h3 : (j ≫ t' k l m ≫ t' l m k ≫ t' m k l) ≫ pullback.fst _ _ =
      a ≫ s k l := by
    apply next_source m k l (j ≫ t' k l m ≫ t' l m k) amk a h2
    simp only [amk, pullback.lift_snd]
    rfl
  apply (cancel_mono p).mp
  have hunique := (Hs k l).2.2 j (p ≫ f k l ≫ h' k) a hj
    (by rw [← Category.assoc, hja, Category.assoc, (Hs k l).2.1])
  apply hunique.unique
  · constructor
    · change (t' k l m ≫ t' l m k ≫ t' m k l) ≫
        pullback.fst _ _ ≫ f k l ≫ h' k = _
      simp only [Category.assoc]
      rw [ht_base, ht_base, ht_base]
    · simpa only [Category.assoc] using h3
  · constructor
    · simp only [Category.id_comp]
    · simpa only [Category.id_comp] using hja

end AlgebraicGeometry
