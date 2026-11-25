/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces

/-! # Pairwise overlaps of universal thickenings

Source: Stacks Project, More on Morphisms, Tag 04F3, proof of Lemma 37.7.1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem universalThickening_iso_source
    {T U V X : Scheme.{u}} (e : T ≅ U) (h : U ⟶ X) (i : U ⟶ V) (p : V ⟶ X)
    (H : IsUniversalFirstOrderThickening h i p) :
    IsUniversalFirstOrderThickening (e.hom ≫ h) (e.hom ≫ i) p := by
  have : IsClosedImmersion i := H.1.1
  refine ⟨⟨inferInstance, ?_⟩, ?_, ?_⟩
  · rw [Scheme.Hom.ker_comp_of_isIso, H.1.2]
  · rw [Category.assoc, H.2.1]
  · intro S S' t b a ht hab
    obtain ⟨c, hc, huniq⟩ := H.2.2 t b (a ≫ e.hom) ht
      (by simpa only [Category.assoc] using hab)
    refine ⟨c, ?_, ?_⟩
    · simpa only [Category.assoc] using hc
    · intro d hd
      exact huniq d (by simpa only [Category.assoc] using hd)

/-- Construct the pairwise overlap restrictions, before choosing any transitions.

Source: Stacks Project, More on Morphisms, Tag 04F3, proof of Lemma 37.7.1,
the general remarks on restriction to opens and the paragraph beginning
"Choose an affine open covering".
(blueprint: lem-weil-pbc-universal-thickening-pairwise-overlaps)

Proof: For k,l let W be the inverse image under C.f k of the open image of C.f l.
The square-zero closed immersion i k is a homeomorphism, so W has a unique
corresponding open W' in Z' k. Set V(k,l)=W'.toScheme and f(k,l)=W'.ι.
The source pullback is canonically isomorphic to W.toScheme because C.f l is
an open immersion. Restrict the universal thickening to W and the whole base,
using the open-pieces theorem, and transport its source along this canonical
isomorphism. This gives s(k,l) and universality for the structure map f(k,l) ≫ h' k.
The restriction equation gives the asserted factorization of s. Membership in
the range of f is membership in W', whose preimage is W; this is exactly the
pointwise equivalence. For k=l the image-preimage open W is the whole chart,
so W' is the whole thickened chart and its inclusion f(k,k) is an isomorphism.
All constructions are indexed by pairs, so the empty cover is vacuous. -/
theorem universalFirstOrderThickening_pairwiseOverlaps
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (V : C.I₀ × C.I₀ → Scheme.{u}) (f : ∀ k l, V (k, l) ⟶ Z' k)
      (s : ∀ k l, pullback (C.f k) (C.f l) ⟶ V (k, l)),
      (∀ k l, IsOpenImmersion (f k l)) ∧
      (∀ k, IsIso (f k k)) ∧
      (∀ k l, IsUniversalFirstOrderThickening
        (pullback.fst (C.f k) (C.f l) ≫ C.f k ≫ h) (s k l) (f k l ≫ h' k)) ∧
      (∀ k l, s k l ≫ f k l = pullback.fst _ _ ≫ i k) ∧
      ∀ k l (z : C.X k),
        i k z ∈ Set.range (f k l) ↔ C.f k z ∈ Set.range (C.f l) := by
  classical
  let W (k l : C.I₀) : (C.X k).Opens := (C.f k) ⁻¹ᵁ (C.f l).opensRange
  have pair (k l : C.I₀) : ∃ (W' : (Z' k).Opens)
      (s : pullback (C.f k) (C.f l) ⟶ W'.toScheme),
      (i k ⁻¹ᵁ W' = W k l) ∧
      IsUniversalFirstOrderThickening
        (pullback.fst (C.f k) (C.f l) ≫ C.f k ≫ h) s (W'.ι ≫ h' k) ∧
      s ≫ W'.ι = pullback.fst _ _ ≫ i k := by
    obtain ⟨W', hpre, _, iW, hW, hW', hiW, hhW, hhW', HW⟩ :=
      (universalFirstOrderThickening_open_pieces (C.f k ≫ h)).2.1
        (i k) (h' k) (H k) (W k l) ⊤ (by simp)
    have HWX : IsUniversalFirstOrderThickening ((W k l).ι ≫ C.f k ≫ h)
        iW (W'.ι ≫ h' k) := by
      rw [← hhW']
      exact (universalFirstOrderThickening_open_pieces ((W k l).ι ≫ C.f k ≫ h)).2.2
        ⊤ hW hhW iW hW' HW
    have heq : Set.range (pullback.fst (C.f k) (C.f l)) = Set.range (W k l).ι := by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
    let e := IsOpenImmersion.isoOfRangeEq (pullback.fst (C.f k) (C.f l)) (W k l).ι heq
    have he : e.hom ≫ (W k l).ι = pullback.fst _ _ :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    refine ⟨W', e.hom ≫ iW, hpre, ?_, ?_⟩
    · simpa only [← Category.assoc, he] using universalThickening_iso_source e _ _ _ HWX
    · rw [Category.assoc, hiW, ← Category.assoc, he]
  choose W' s hpre Hs hsf using pair
  refine ⟨fun kl ↦ (W' kl.1 kl.2).toScheme, fun k l ↦ (W' k l).ι, s,
    fun k l ↦ inferInstance, ?_, Hs, hsf, ?_⟩
  · intro k
    have hW : W k k = ⊤ := by
      ext z
      change C.f k z ∈ Set.range (C.f k) ↔ True
      exact iff_true_intro ⟨z, rfl⟩
    have htop : W' k k = ⊤ := by
      obtain ⟨A, hA, huniq⟩ :=
        ((universalFirstOrderThickening_open_pieces (C.f k ≫ h)).1
          (i k) (h' k) (H k).1).2 ⊤
      exact (huniq (W' k k) ((hpre k k).trans hW)).trans
        (huniq ⊤ (by simp)).symm
    change IsIso (W' k k).ι
    rw [htop]
    change IsIso (Z' k).topIso.hom
    infer_instance
  · intro k l z
    rw [Scheme.Opens.range_ι]
    change z ∈ i k ⁻¹ᵁ W' k l ↔ _
    rw [hpre]
    rfl

end AlgebraicGeometry
