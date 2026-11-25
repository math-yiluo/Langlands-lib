/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import all WeilConjectures.AlgebraicGeometry.PicardFiberRankClopen
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Ordinary local normal forms of the reference-rank predicate

Source: Stacks Project, Tag 0BDP, first three proof paragraphs, with the empty
and mixed-fibre cases of the unrestricted chart argument.
(blueprint: lem-sc-picard-rank-match-direct-image-normal-form).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private noncomputable def tensorRankIso {A B : Scheme.{u}} (g : A ⟶ B) :
    Modules.tensorPullback g ≅ Modules.pullback g :=
  (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction g)

private theorem tensor_rank {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules)
    (r : ℕ) (hr : M.IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback g).obj M).IsFiniteLocallyFreeOfRank r := by
  have := hr
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ((tensorRankIso g).app M).symm

private theorem empty_rank {A : Scheme.{u}} [IsEmpty A] (M : A.Modules) (r : ℕ) :
    M.IsFiniteLocallyFreeOfRank r := by
  apply Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top M (fun x : A ↦ isEmptyElim x)
  · apply eq_top_iff.mpr
    intro x
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x

private theorem zero_rank {A : Scheme.{u}} (M : A.Modules) (hM : IsZero M) :
    M.IsFiniteLocallyFreeOfRank 0 := by
  let Z : A.Modules := SheafOfModules.free (ULift.{u} (Fin 0))
  have hZ : IsZero Z := by
    apply (IsZero.iff_id_eq_zero Z).mpr
    apply SheafOfModules.free_hom_ext
    intro i
    exact isEmptyElim i
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hZ.iso hM)

private theorem homogeneous_match {X S : Scheme.{u}} (f : X ⟶ S)
    (E F : X.Modules) {U : S.Opens} (r : ℕ)
    (himage : ∀ t : U.toScheme, (U.ι t) ∈ Set.range f)
    (hE : ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
      ((Modules.tensorPullback (pullback.fst f (g ≫ U.ι))).obj E)
        |>.IsFiniteLocallyFreeOfRank r) :
    ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
      PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔
        ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
          ((Modules.pushforward (pullback.snd f (h ≫ g ≫ U.ι))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g ≫ U.ι))).obj F))
              |>.IsFiniteLocallyFreeOfRank r := by
  classical
  intro T g
  constructor
  · intro hm T' h
    let M := (Modules.pushforward (pullback.snd f (h ≫ g ≫ U.ι))).obj
      ((Modules.tensorPullback (pullback.fst f (h ≫ g ≫ U.ι))).obj F)
    have hl (t : T') : ∃ V : T'.Opens, t ∈ V ∧
        ((Modules.tensorPullback V.ι).obj M).IsFiniteLocallyFreeOfRank r := by
      obtain ⟨V, ht, n, hM, hn⟩ := hm h t
      have hr := hE V.toScheme (V.ι ≫ h ≫ g)
      have hx : (⟨t, ht⟩ : V.toScheme) ∈
          Set.range (pullback.snd f (V.ι ≫ h ≫ g ≫ U.ι)) := by
        rw [Pullback.range_snd]
        exact himage ((V.ι ≫ h ≫ g) ⟨t, ht⟩)
      obtain ⟨x, _⟩ := hx
      have heq : n = r := rank_unique _ n r hn hr x
      exact ⟨V, ht, heq ▸ hM⟩
    choose V ht hv using hl
    apply Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion M (fun t ↦ (V t).ι)
    · apply eq_top_iff.mpr
      intro t _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, by
        rw [Scheme.Opens.opensRange_ι]
        exact ht t⟩
    · intro t
      have := hv t
      exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ((tensorRankIso (V t).ι).app M)
  · intro hd T' h t
    refine ⟨⊤, by trivial, r, tensor_rank _ _ r (hd T' h), ?_⟩
    exact hE (⊤ : T'.Opens).toScheme ((⊤ : T'.Opens).ι ≫ h ≫ g)

/-- Locally, the reference-rank predicate is either universal fixed-rank freeness
of the ordinary direct image, or the condition that the test scheme is empty.
No derived category, complex, perfectness, or Tor bound occurs in this assertion.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs; the empty and
mixed-fibre adaptation in the unrestricted perfect-chart argument.
(blueprint: lem-sc-picard-rank-match-direct-image-normal-form).

Proof: Let X_r be the clopen local rank-r locus of E. Flatness and local finite
presentation make f open; properness makes f closed, so f(X_r), f(X minus X_r)
and f(X) are clopen. If the fibre at s is nonempty and has one rank r, use the
neighbourhood f(X) minus f(X minus X_r). Every fibre there is nonempty of rank r,
including after arbitrary field extension. Pullback preserves local rank. In any
local witness for the predicate, the reference rank must equal r by comparing
finranks at a point of its nonempty fibre. Fixed-rank freeness of the direct image
is local, so the witnesses give global rank-r freeness on every further test.
Conversely, restrict the globally rank-r direct image to the top open and use
the already rank-r reference bundle to supply witnesses.
If the fibre at s is empty, use S minus f(X). Every base-changed source is empty,
its modules are zero, and its direct image is zero. Use rank zero on every test;
the reference condition on the empty source is vacuous.
Otherwise choose two different local ranks a and c in the fibre and use
f(X_a) intersect f(X_c). A nonempty test has a residue-field point, and its fibre
has points of both ranks, since nonempty fibres persist under field extension.
Any reference witness over that point would have both ranks a and c, contrary
to stalk invariant basis number. Thus the predicate forces the test to be empty.
For empty tests the universal pointwise condition is vacuous. These cases exhaust
all fibres. Rank zero, empty sources, and nonreduced tests are included. -/
theorem exists_picardRankMatchDirectImageNormalForm
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      ((∃ r : ℕ, ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔
          ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
            SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((Modules.pushforward (pullback.snd f (h ≫ g ≫ U.ι))).obj
                ((Modules.tensorPullback (pullback.fst f (h ≫ g ≫ U.ι))).obj F)) r) ∨
      (∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔ IsEmpty T)) := by
  classical
  have hRange : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  by_cases hs : s ∈ Set.range f
  · by_cases hrank : ∃ r : ℕ, ∀ x : X, f x = s → x ∈ localRank E r
    · obtain ⟨r, hr⟩ := hrank
      have hb : IsClopen (f '' (localRank E r)ᶜ) :=
        ⟨f.isClosedMap _ (localRank_isClopen E r).compl.isClosed,
          f.isOpenMap _ (localRank_isClopen E r).compl.isOpen⟩
      let U : S.Opens :=
        ⟨Set.range f ∩ (f '' (localRank E r)ᶜ)ᶜ, hRange.isOpen.inter hb.compl.isOpen⟩
      have hsU : s ∈ U := by
        refine ⟨hs, ?_⟩
        rintro ⟨x, hx, hxs⟩
        exact hx (hr x hxs)
      have hE (T : Scheme.{u}) (g : T ⟶ U.toScheme) :
          ((Modules.tensorPullback (pullback.fst f (g ≫ U.ι))).obj E)
            |>.IsFiniteLocallyFreeOfRank r := by
        rw [tensorPullback_rank_iff]
        intro y
        by_contra hy
        have ht := (g ((pullback.snd f (g ≫ U.ι)) y)).property.2
        apply ht
        refine ⟨(pullback.fst f (g ≫ U.ι)) y, hy, ?_⟩
        rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
        rfl
      exact ⟨U, hsU, Or.inl ⟨r,
        homogeneous_match f E F r (fun t ↦ t.property.1) hE⟩⟩
    · obtain ⟨x, hx⟩ := hs
      obtain ⟨a, ha⟩ := exists_localRank E x
      have hbad : ∃ y : X, f y = s ∧ y ∉ localRank E a := by
        by_contra h
        apply hrank
        refine ⟨a, ?_⟩
        intro y hy
        by_contra hn
        exact h ⟨y, hy, hn⟩
      obtain ⟨y, hy, hya⟩ := hbad
      let U : S.Opens :=
        ⟨f '' localRank E a ∩ f '' (localRank E a)ᶜ,
          (f.isOpenMap _ (localRank_isOpen E a)).inter
            (f.isOpenMap _ (localRank_isClopen E a).compl.isOpen)⟩
      refine ⟨U, ⟨⟨x, ha, hx⟩, ⟨y, hya, hy⟩⟩, Or.inr ?_⟩
      intro T g
      constructor
      · intro hm
        refine ⟨fun t ↦ ?_⟩
        obtain ⟨V, ht, n, _, hn⟩ := hm (𝟙 T) t
        let k := V.ι ≫ (𝟙 T) ≫ g ≫ U.ι
        have hkn : ∀ z : (pullback f k : Scheme.{u}),
            (pullback.fst f k) z ∈ localRank E n :=
          (tensorPullback_rank_iff _ E n).mp hn
        obtain ⟨xa, hxa, hfa⟩ := (g t).property.1
        obtain ⟨xb, hxb, hfb⟩ := (g t).property.2
        have lift_point (z : X) (hz : f z = (U.ι (g t))) :
            z ∈ Set.range (pullback.fst f k) := by
          rw [Pullback.range_fst]
          exact ⟨⟨t, ht⟩, hz.symm⟩
        obtain ⟨za, hza⟩ := lift_point xa hfa
        obtain ⟨zb, hzb⟩ := lift_point xb hfb
        have hna : xa ∈ localRank E n := hza ▸ hkn za
        have heq : n = a := localRank_unique E hna hxa
        have hnb : xb ∈ localRank E n := hzb ▸ hkn zb
        exact hxb (heq ▸ hnb)
      · intro hempty
        have := hempty
        intro T' h t
        exact isEmptyElim (h t)
  · let U : S.Opens := ⟨(Set.range f)ᶜ, hRange.compl.isOpen⟩
    have empty_source (T : Scheme.{u}) (g : T ⟶ U.toScheme) :
        IsEmpty (pullback f (g ≫ U.ι) : Scheme.{u}) := by
      refine ⟨fun y ↦ ?_⟩
      have ht := (g ((pullback.snd f (g ≫ U.ι)) y)).property
      apply ht
      refine ⟨(pullback.fst f (g ≫ U.ι)) y, ?_⟩
      rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
      rfl
    have hD (T : Scheme.{u}) (g : T ⟶ U.toScheme) :
        ((Modules.pushforward (pullback.snd f (g ≫ U.ι))).obj
          ((Modules.tensorPullback (pullback.fst f (g ≫ U.ι))).obj F))
            |>.IsFiniteLocallyFreeOfRank 0 := by
      have := empty_source T g
      exact zero_rank _ ((Modules.pushforward _).map_isZero (Modules.isZero_of_isEmpty _))
    refine ⟨U, hs, Or.inl ⟨0, ?_⟩⟩
    intro T g
    constructor
    · intro _ T' h
      exact hD T' (h ≫ g)
    · intro _ T' h t
      refine ⟨⊤, by trivial, 0, tensor_rank _ _ 0 (hD T' (h ≫ g)), ?_⟩
      have : IsEmpty (pullback f ((⊤ : T'.Opens).ι ≫ h ≫ g ≫ U.ι) :
          Scheme.{u}) := by
        simpa only [Category.assoc] using
          empty_source (⊤ : T'.Opens).toScheme ((⊤ : T'.Opens).ι ≫ h ≫ g)
      exact empty_rank _ 0

end AlgebraicGeometry.Scheme
