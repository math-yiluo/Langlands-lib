/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.ConstructibleSheaf.AffineStratification
import WeilConjectures.AlgebraicGeometry.NoetherNormalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Separating closed sections over affine strata

Source: Stacks Project, Tag 095K, proof of `lemma-decompose-quasi-finite-morphism`,
final paragraph (blueprint: lem-weil-pbc-closed-section-affine-partition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem affine_partition_compatible_closed
    {X : Scheme.{u}} [IsAffine X] [IsNoetherian X]
    (d : ℕ) (C : Fin d → Set X) (hC : ∀ i, IsClosed (C i)) :
    ∃ (m : ℕ) (R : Fin m → Scheme.{u}) (r : ∀ a, R a ⟶ X),
      (∀ a, IsAffine (R a) ∧ IsReduced (R a)) ∧
      (∀ x : X, ∃ (a : Fin m) (z : R a), r a z = x) ∧
      ∀ a i, Set.range (r a) ⊆ C i ∨ Disjoint (Set.range (r a)) (C i) := by
  classical
  let B := Fin d → Bool
  let A (b : B) : Set X :=
    (⋂ i, if b i = true then C i else Set.univ) ∩
      (⋂ i, if b i = true then Set.univ else (C i)ᶜ)
  have hA (b : B) : IsLocallyClosed (A b) := by
    apply IsLocallyClosed.inter
    · apply IsClosed.isLocallyClosed
      apply isClosed_iInter
      intro i
      split_ifs
      · exact hC i
      · exact isClosed_univ
    · apply IsOpen.isLocallyClosed
      apply isOpen_iInter_of_finite
      intro i
      split_ifs
      · exact isOpen_univ
      · exact (hC i).isOpen_compl
  have hD (b : B) : ∃ (D : Scheme.{u}) (ι : D ⟶ X),
      IsImmersion ι ∧ Set.range ι = A b := by
    obtain ⟨D, j, hj, hjrange⟩ :=
      Scheme.exists_isImmersion_range_eq_of_isLocallyClosed
        ((hA b).preimage X.isoSpec.inv.continuous)
    let := hj
    refine ⟨D, j ≫ X.isoSpec.inv, inferInstance, ?_⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hjrange]
    exact Set.image_preimage_eq _ (Scheme.Hom.homeomorph X.isoSpec.inv).surjective
  choose D j hj hjrange using hD
  have hDN (b : B) : TopologicalSpace.NoetherianSpace (D b) :=
    (j b).isEmbedding.isInducing.noetherianSpace
  let := hDN
  obtain ⟨n, Z, s, hs, hc⟩ : ∃ (n : B → ℕ) (Z : ∀ b, Fin (n b) → Scheme.{u})
      (s : ∀ b k, Z b k ⟶ D b),
      (∀ b k, IsImmersion (s b k) ∧ IsAffine (Z b k) ∧ IsReduced (Z b k)) ∧
      (∀ b x, ∃! k, x ∈ Set.range (s b k)) := by
    have hh (b : B) := Scheme.exists_partition_isImmersion_isAffine_isReduced (D b)
    choose n Z s hs hc using hh
    exact ⟨n, Z, s, hs, hc⟩
  let I := Σ b : B, Fin (n b)
  let e := Fintype.equivFin I
  let R (a : Fin (Fintype.card I)) := Z (e.symm a).1 (e.symm a).2
  let r (a : Fin (Fintype.card I)) : R a ⟶ X :=
    s (e.symm a).1 (e.symm a).2 ≫ j (e.symm a).1
  have hr (a : Fin (Fintype.card I)) : Set.range (r a) ⊆ A (e.symm a).1 := by
    intro x ⟨y, hy⟩
    rw [← hjrange]
    exact ⟨s (e.symm a).1 (e.symm a).2 y, hy⟩
  have hcov' : ⋃ i : I, Set.range (s i.1 i.2 ≫ j i.1) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let b : B := fun i ↦ decide (x ∈ C i)
    have hx : x ∈ A b := by
      constructor <;> apply Set.mem_iInter.mpr <;> intro i <;>
        by_cases hi : x ∈ C i <;> simp [b, hi]
    rw [← hjrange] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨k, ⟨z, hz⟩, _⟩ := hc b y
    exact Set.mem_iUnion.mpr ⟨⟨b, k⟩, z, by
      simpa only [Scheme.Hom.comp_apply, hz] using hy⟩
  have hcov : ⋃ a, Set.range (r a) = Set.univ :=
    (Function.Surjective.iUnion_comp e.symm.surjective
      (fun i : I ↦ Set.range (s i.1 i.2 ≫ j i.1))).trans hcov'
  refine ⟨Fintype.card I, R, r, fun a ↦ (hs _ _).2, ?_, ?_⟩
  · intro x
    have hx : x ∈ ⋃ a, Set.range (r a) := hcov ▸ Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  · intro a i
    by_cases hi : (e.symm a).1 i = true
    · left
      intro x hx
      have := Set.mem_iInter.mp (hr a hx).1 i
      simpa only [ite_eq_left hi] using this
    · right
      apply Set.disjoint_left.mpr
      intro x hx hxi
      have := Set.mem_iInter.mp (hr a hx).2 i
      have hh : x ∉ C i := by simpa only [ite_eq_right hi, Set.mem_compl_iff] using this
      exact hh hxi

private theorem isPullback_section_lift
    {X Y W R : Scheme.{u}} (p : W ⟶ X) (j : Y ⟶ W) [Mono j] (h : Y ⟶ X)
    (hjp : j ≫ p = h) (s : X ⟶ W) (hsp : s ≫ p = 𝟙 X)
    (r : R ⟶ X) (g : R ⟶ Y) (hgj : g ≫ j = r ≫ s)
    (hgh : g ≫ h = r) :
    IsPullback r (pullback.lift g (𝟙 R) (by simpa using hgh)) s
      (pullback.fst h r ≫ j) := by
  let t : R ⟶ pullback h r := pullback.lift g (𝟙 R) (by simpa using hgh)
  have htf : t ≫ pullback.fst h r = g := pullback.lift_fst _ _ _
  have hts : t ≫ pullback.snd h r = 𝟙 R := pullback.lift_snd _ _ _
  change IsPullback r t s (pullback.fst h r ≫ j)
  have hfst (c : PullbackCone s (pullback.fst h r ≫ j)) :
      (c.snd ≫ pullback.snd h r) ≫ r = c.fst := by
    calc
      (c.snd ≫ pullback.snd h r) ≫ r = c.snd ≫ pullback.fst h r ≫ h := by
        rw [Category.assoc, ← pullback.condition]
      _ = (c.snd ≫ (pullback.fst h r ≫ j)) ≫ p := by
        simp only [Category.assoc, hjp]
      _ = (c.fst ≫ s) ≫ p := by rw [c.condition]
      _ = c.fst := by rw [Category.assoc, hsp, Category.comp_id]
  have hsnd (c : PullbackCone s (pullback.fst h r ≫ j)) :
      (c.snd ≫ pullback.snd h r) ≫ t = c.snd := by
    apply pullback.hom_ext
    · rw [Category.assoc, htf]
      apply (cancel_mono j).mp
      calc
        (c.snd ≫ pullback.snd h r ≫ g) ≫ j =
            ((c.snd ≫ pullback.snd h r) ≫ r) ≫ s := by
          simp only [Category.assoc, hgj]
        _ = c.fst ≫ s := by rw [hfst]
        _ = (c.snd ≫ pullback.fst h r) ≫ j := by
          simpa only [Category.assoc] using c.condition
    · simp only [Category.assoc, hts, Category.comp_id]
  refine ⟨⟨by rw [← Category.assoc, htf, hgj]⟩,
    ⟨PullbackCone.IsLimit.mk _ (fun c ↦ c.snd ≫ pullback.snd h r) hfst hsnd ?_⟩⟩
  intro c m hm₁ hm₂
  simpa only [Category.assoc, hts, Category.comp_id] using
    congrArg (fun f ↦ f ≫ pullback.snd h r) hm₂

private theorem select_disjoint_closed_sections
    {X Y W R : Scheme.{u}} [IsReduced R]
    (p : W ⟶ X) (j : Y ⟶ W) [IsClosedImmersion j] (h : Y ⟶ X)
    (hjp : j ≫ p = h) (n : ℕ) (s : Fin n → (X ⟶ W))
    (hs : ∀ k, IsClosedImmersion (s k)) (hsp : ∀ k, s k ≫ p = 𝟙 X)
    (hcover : ∀ w : W, ∃ (k : Fin n) (x : X), s k x = w)
    (r : R ⟶ X)
    (hinc : ∀ k, Set.range r ⊆ Set.range (pullback.snd j (s k)) ∨
      Disjoint (Set.range r) (Set.range (pullback.snd j (s k))))
    (heq : ∀ k l, Set.range r ⊆ Set.range (pullback.fst (s k) (s l)) ∨
      Disjoint (Set.range r) (Set.range (pullback.fst (s k) (s l)))) :
    ∃ (q : ℕ) (t : Fin q → (R ⟶ pullback h r)),
      (∀ k, IsClosedImmersion (t k) ∧ IsIso (t k ≫ pullback.snd h r)) ∧
      Pairwise (fun k l ↦ Disjoint (Set.range (t k)) (Set.range (t l))) ∧
      ∀ y : ↥(pullback h r), ∃ (k : Fin q) (z : R), t k z = y := by
  classical
  let := hs
  let K := {k : Fin n // Set.range r ⊆ Set.range (pullback.snd j (s k))}
  have hg (k : K) : ∃ g : R ⟶ Y, g ≫ j = r ≫ s k.1 := by
    apply ExistsUnique.exists
    apply IsClosedImmersion.existsUnique_fac_of_range_subset_range
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := k.2 ⟨x, rfl⟩
    refine ⟨pullback.fst j (s k.1) y, ?_⟩
    have hh := congrArg (fun f ↦ f y) (pullback.condition (f := j) (g := s k.1))
    simpa only [Scheme.Hom.comp_apply, hy] using hh
  choose g hgj using hg
  have hgh (k : K) : g k ≫ h = r := by
    rw [← hjp, ← Category.assoc, hgj, Category.assoc, hsp, Category.comp_id]
  let t (k : K) : R ⟶ pullback h r :=
    pullback.lift (g k) (𝟙 R) (by simpa using hgh k)
  have hts (k : K) : t k ≫ pullback.snd h r = 𝟙 R := pullback.lift_snd _ _ _
  have htf (k : K) : t k ≫ pullback.fst h r = g k := pullback.lift_fst _ _ _
  have hsq (k : K) : IsPullback r (t k) (s k.1) (pullback.fst h r ≫ j) :=
    isPullback_section_lift p j h hjp (s k.1) (hsp k.1) r (g k) (hgj k) (hgh k)
  have htc (k : K) : IsClosedImmersion (t k) :=
    MorphismProperty.of_isPullback (hsq k) (hs k.1)
  have htd (k l : K) : t k = t l ∨ Disjoint (Set.range (t k)) (Set.range (t l)) := by
    rcases heq k.1 l.1 with hfull | hempty
    · left
      obtain ⟨e, he, _⟩ :=
        IsClosedImmersion.existsUnique_fac_of_range_subset_range
          (pullback.fst (s k.1) (s l.1)) r hfull
      have he' : e ≫ pullback.snd (s k.1) (s l.1) = r := by
        calc
          e ≫ pullback.snd (s k.1) (s l.1) =
              e ≫ pullback.snd (s k.1) (s l.1) ≫ s l.1 ≫ p := by rw [hsp]; simp
          _ = e ≫ pullback.fst (s k.1) (s l.1) ≫ s k.1 ≫ p := by
            rw [← pullback.condition_assoc]
          _ = r := by rw [hsp, Category.comp_id, he]
      have hrs : r ≫ s k.1 = r ≫ s l.1 := by
        calc
          r ≫ s k.1 = (e ≫ pullback.fst (s k.1) (s l.1)) ≫ s k.1 :=
            congrArg (fun f ↦ f ≫ s k.1) he.symm
          _ = (e ≫ pullback.snd (s k.1) (s l.1)) ≫ s l.1 := by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
          _ = r ≫ s l.1 := congrArg (fun f ↦ f ≫ s l.1) he'
      apply pullback.hom_ext
      · rw [htf, htf]
        apply (cancel_mono j).mp
        rw [hgj, hgj, hrs]
      · rw [hts, hts]
    · right
      apply Set.disjoint_left.mpr
      rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
      have hxy : y = x := by
        have hh := congrArg (fun z ↦ pullback.snd h r z) hy
        change (t l ≫ pullback.snd h r) y = (t k ≫ pullback.snd h r) x at hh
        simp only [hts] at hh
        exact hh
      subst y
      have hsx : s k.1 (r x) = s l.1 (r x) := by
        have hh := congrArg (fun z ↦ (pullback.fst h r ≫ j) z) hy
        have hk := (hsq k).w
        have hl := (hsq l).w
        change (t l ≫ pullback.fst h r ≫ j) x =
          (t k ≫ pullback.fst h r ≫ j) x at hh
        rw [← hl, ← hk] at hh
        exact hh.symm
      obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback (s k.1) (s l.1)) (r x) (r x) hsx
      exact Set.disjoint_left.mp hempty ⟨x, rfl⟩ ⟨z, hz⟩
  have hcov : ∀ y : ↥(pullback h r), ∃ (k : K) (z : R), t k z = y := by
    intro y
    obtain ⟨k, x, hx⟩ := hcover (j (pullback.fst h r y))
    have hxr : x = r (pullback.snd h r y) := by
      have hh := congrArg (fun w ↦ p w) hx
      change (s k ≫ p) x = (pullback.fst h r ≫ j ≫ p) y at hh
      rw [hsp, hjp, pullback.condition] at hh
      exact hh
    have hmem : x ∈ Set.range (pullback.snd j (s k)) := by
      obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback j (s k)) (pullback.fst h r y) x hx.symm
      exact ⟨z, hz⟩
    have hk : Set.range r ⊆ Set.range (pullback.snd j (s k)) := by
      rcases hinc k with hfull | hempty
      · exact hfull
      · exact False.elim (Set.disjoint_left.mp hempty ⟨_, hxr.symm⟩ hmem)
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback (hsq ⟨k, hk⟩) x y hx
    exact ⟨⟨k, hk⟩, z, hz⟩
  let H := Set.range t
  let : Fintype H := (Set.finite_range t).fintype
  let e := Fintype.equivFin H
  let t' (a : Fin (Fintype.card H)) : R ⟶ pullback h r := (e.symm a).1
  refine ⟨Fintype.card H, t', ?_, ?_, ?_⟩
  · intro a
    obtain ⟨k, hk⟩ := (e.symm a).2
    change IsClosedImmersion (e.symm a).1 ∧ IsIso ((e.symm a).1 ≫ _)
    rw [← hk, hts]
    exact ⟨htc k, inferInstance⟩
  · intro a b hab
    obtain ⟨k, hk⟩ := (e.symm a).2
    obtain ⟨l, hl⟩ := (e.symm b).2
    rcases htd k l with hkl | hd
    · exact False.elim (hab (e.symm.injective (Subtype.ext (hk.symm.trans (hkl.trans hl)))))
    · simpa only [t', hk, hl] using hd
  · intro y
    obtain ⟨k, z, hz⟩ := hcov y
    exact ⟨e ⟨t k, k, rfl⟩, z, by simpa only [t', e.symm_apply_apply] using hz⟩

/-- A closed subscheme of an affine scheme covered by finitely many closed sections is
covered by disjoint closed sections after a finite reduced affine partition of the base.

Source: Stacks Project, Tag 095K, final paragraph of
`lemma-decompose-quasi-finite-morphism`.
(blueprint: lem-weil-pbc-closed-section-affine-partition)

Proof: Replace each Z_k by the base using its isomorphism Z_k -> X. The inverse image
of Y under each section and the intersection of each pair of sections are closed subschemes
of X, by base change of closed immersions. Form the finitely
many Boolean atoms of their closed images. Realize an atom as an open subscheme of the
closed subscheme cut out by the sum of the relevant defining ideals. Each atom is
Noetherian. Partition it into finitely many reduced affine locally closed subschemes.
The resulting maps R_a -> X cover X. Every pulled-back incidence and equalizer has
empty image or all of R_a. In the latter case it is a surjective closed immersion into
a reduced scheme, hence an isomorphism. Thus each section is either disjoint from Y_R
or factors through it, and two retained sections coincide or have disjoint images.
To prove coverage, project a point of Y_R to W and choose an original section through
it. Its incidence with Y meets R, hence contains all of R. The square formed by this
section, its lift R -> Y_R, the map R -> X, and Y_R -> W is a pullback: a compatible
cone lifts by its projection to R. Thus the point lifts to R, and this also proves that
R -> Y_R is closed by base change. Take the finite set of distinct lifted section
morphisms and reindex it by Fin q. Their
composites to R_a are isomorphisms, their images are pairwise disjoint, and they cover
Y_R. When Y_R is empty, take zero sections. Empty atoms may be retained; for an empty
base take an empty partition. This construction permits repeated sections and handles
the zero ring. -/
theorem exists_closed_section_affine_partition
    {X Y W : Scheme.{u}} [IsAffine X] [IsNoetherian X] [IsAffine W]
    (h : Y ⟶ X) (p : W ⟶ X) (j : Y ⟶ W) [IsClosedImmersion j]
    (hjp : j ≫ p = h) (n : ℕ) (Z : Fin n → Scheme.{u})
    (s : ∀ k, Z k ⟶ W)
    (hs : ∀ k, IsClosedImmersion (s k) ∧ IsIso (s k ≫ p))
    (hcover : ∀ w : W, ∃ (k : Fin n) (z : Z k), s k z = w) :
    ∃ (m : ℕ) (R : Fin m → Scheme.{u}) (r : ∀ a, R a ⟶ X),
      (∀ a, IsAffine (R a) ∧ IsReduced (R a)) ∧
      (∀ x : X, ∃ (a : Fin m) (z : R a), r a z = x) ∧
      ∀ a : Fin m, ∃ (q : ℕ) (t : Fin q → (R a ⟶ pullback h (r a))),
        (∀ k, IsClosedImmersion (t k) ∧ IsIso (t k ≫ pullback.snd h (r a))) ∧
        Pairwise (fun k l ↦ Disjoint (Set.range (t k)) (Set.range (t l))) ∧
        ∀ y : ↥(pullback h (r a)), ∃ (k : Fin q) (z : R a), t k z = y := by
  classical
  have hsi (k : Fin n) : IsIso (s k ≫ p) := (hs k).2
  let := hsi
  let s' (k : Fin n) : X ⟶ W := inv (s k ≫ p) ≫ s k
  have hs' (k : Fin n) : IsClosedImmersion (s' k) := by
    have := (hs k).1
    dsimp [s']
    infer_instance
  have hsp' (k : Fin n) : s' k ≫ p = 𝟙 X := by
    simp only [s', Category.assoc, IsIso.inv_hom_id]
  have hc' : ∀ w : W, ∃ (k : Fin n) (x : X), s' k x = w := by
    intro w
    obtain ⟨k, z, hz⟩ := hcover w
    refine ⟨k, (s k ≫ p) z, ?_⟩
    change ((s k ≫ p) ≫ s' k) z = w
    simpa only [s', ← Category.assoc, IsIso.hom_inv_id, Category.id_comp] using hz
  let := hs'
  let I := Fin n ⊕ (Fin n × Fin n)
  let C : I → Set X := Sum.elim
    (fun k ↦ Set.range (pullback.snd j (s' k)))
    (fun kl ↦ Set.range (pullback.fst (s' kl.1) (s' kl.2)))
  have hC (i : I) : IsClosed (C i) := by
    cases i with
    | inl k => exact (pullback.snd j (s' k)).isClosedEmbedding.isClosed_range
    | inr kl => exact (pullback.fst (s' kl.1) (s' kl.2)).isClosedEmbedding.isClosed_range
  let e := Fintype.equivFin I
  obtain ⟨m, R, r, hR, hc, hcomp⟩ := affine_partition_compatible_closed
    (Fintype.card I) (fun i ↦ C (e.symm i)) (fun i ↦ hC _)
  refine ⟨m, R, r, hR, hc, ?_⟩
  intro a
  have := (hR a).2
  apply select_disjoint_closed_sections p j h hjp n s' hs' hsp' hc' (r a)
  · intro k
    simpa only [e.symm_apply_apply, C, Sum.elim_inl] using hcomp a (e (.inl k))
  · intro k l
    simpa only [e.symm_apply_apply, C, Sum.elim_inr] using hcomp a (e (.inr (k, l)))

end AlgebraicGeometry
