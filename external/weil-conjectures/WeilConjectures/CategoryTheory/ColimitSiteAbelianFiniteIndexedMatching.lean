/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.ColimitSiteAbelianPairwiseEventualMatching
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma

/-! # Finite matching equations at a common transition

Source: Stacks Project, Sites, Tag 0A35, finite-cover equalizer paragraph.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Composition of unit-compatible comparison maps for arbitrary target sheaves.
The target sheaves and the two prescribed transposes need not be inverse images
of the source sheaf. Injectivity of the adjunction hom-equivalence proves the
map equality after substituting the functor equations; evaluation gives the result.
-/
theorem sheaf_comparison_comp
    {C D E Z : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory E] [SmallCategory Z]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (Q : GrothendieckTopology Z)
    (f : C ⥤ D) (g : D ⥤ E) (k : E ⥤ Z)
    (h : C ⥤ E) (l : C ⥤ Z) (m : D ⥤ Z)
    [f.IsContinuous T S] [g.IsContinuous S R] [k.IsContinuous R Q]
    [h.IsContinuous T R] [l.IsContinuous T Q] [m.IsContinuous S Q]
    (w₁ : f ⋙ g = h) (w₂ : h ⋙ k = l) (w₃ : g ⋙ k = m)
    (G : Sheaf T AddCommGrpCat.{u})
    (H : Sheaf R AddCommGrpCat.{u}) (K : Sheaf Q AddCommGrpCat.{u})
    (η : G ⟶ (h.sheafPushforwardContinuous AddCommGrpCat.{u} T R).obj H)
    (ζ : G ⟶ (l.sheafPushforwardContinuous AddCommGrpCat.{u} T Q).obj K)
    (a : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj H)
    (b : H ⟶
      (k.sheafPushforwardContinuous AddCommGrpCat.{u} R Q).obj K)
    (c : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (m.sheafPushforwardContinuous AddCommGrpCat.{u} S Q).obj K)
    (ha : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (η.hom.app (op X)))
    (hb : ∀ X : C,
      Arrow.mk (η.hom.app (op X) ≫ b.hom.app (op (h.obj X))) =
      Arrow.mk (ζ.hom.app (op X)))
    (hc : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ c.hom.app (op (f.obj X))) =
      Arrow.mk (ζ.hom.app (op X))) (Y : D) :
    Arrow.mk (a.hom.app (op Y) ≫ b.hom.app (op (g.obj Y))) =
      Arrow.mk (c.hom.app (op Y)) := by
  subst h
  subst l
  subst m
  have eq : a ≫ (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).map b = c := by
    apply ((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).homEquiv G _).injective
    ext1
    apply NatTrans.ext
    funext X
    apply (Arrow.mk_inj _ _).mp
    have haX := ha (unop X)
    have hbX := hb (unop X)
    have hcX := hc (unop X)
    change Arrow.mk
      (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app X ≫
        (a.hom.app (op (f.obj (unop X))) ≫
          b.hom.app (op (g.obj (f.obj (unop X)))))) = _
    rw [← Category.assoc, (Arrow.mk_inj _ _).mp haX]
    exact hbX.trans hcX.symm
  exact congrArg (fun z ↦ Arrow.mk (z.hom.app (op Y))) eq

private theorem arrow_values_iff {A B C : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (h : Arrow.mk f = Arrow.mk g) (x y : A) :
    f x = f y ↔ g x = g y := by
  have hC : B = C := congrArg Arrow.right h
  subst C
  rw [(Arrow.mk_inj _ _).mp h]

private theorem finite_refinement
    {C : Type u} [SmallCategory C] [IsFiltered C]
    (t : C) (L : Type u) [Finite L]
    (R : ∀ s : C, (t ⟶ s) → L → Prop)
    (hR : ∀ (s s' : C) (b : t ⟶ s) (c : s ⟶ s') (l : L),
      R s b l → R s' (b ≫ c) l)
    (h : ∀ l : L, ∃ (s : C) (b : t ⟶ s), R s b l) :
    ∃ (s : C) (b : t ⟶ s), ∀ l : L, R s b l := by
  classical
  let _ : Fintype L := Fintype.ofFinite L
  have hs (a : Finset L) : ∃ (s : C) (b : t ⟶ s), ∀ l ∈ a, R s b l := by
    induction a using Finset.induction_on with
    | empty => exact ⟨t, 𝟙 t, by simp⟩
    | @insert l a hla ih =>
      obtain ⟨s, b, hb⟩ := ih
      obtain ⟨s', b', hb'⟩ := h l
      obtain ⟨s'', c, c', hw⟩ := IsFiltered.span b b'
      refine ⟨s'', b ≫ c, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [hw]
        exact hR s' s'' b' c' _ hb'
      · exact hR s s'' b c k (hb k hk)
  obtain ⟨s, b, hb⟩ := hs Finset.univ
  exact ⟨s, b, fun l ↦ hb l (Finset.mem_univ l)⟩

/-- A finite indexed family becomes matching under the prescribed stage comparison.
Source: Stacks Project, Sites, Tag 0A35, finite-cover matching equalizer paragraph
and the unit-compatible adjunction paragraph; Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-abelian-finite-indexed-matching)

Proof: For each ordered pair of arrows in the finite set T.uncurry take its
covering pullback at t.right. Apply the named pairwise eventual matching theorem
to its two projections to obtain a transition equating those two restrictions.
This is the sole open step; its module documents the independent section-colimit
route and avoids the cyclic stage-image-sheaf construction.

There are finitely many ordered pairs. Uniqueness of adjuncts using h-theta
proves the composition law of theta, including endpoint equality transports.
Hence every equality persists under further transition. Induct on the finite
set of pairs: for a new pair use IsFiltered.span in Under i to combine its
witnessing arrow out of t with the common arrow for the previous pairs. The
commuting span and persistence preserve all equations. The empty finite set
uses the identity arrow. This gives one transition b killing all differences.
Naturality of theta identifies these images with restrictions of
the indexed transitioned sections along the mapped pullback projections.
By hpullback the mapped square is a pullback. Any pair of arrows to the mapped
cover with equal composites factors through that square, so restricting its
established equality proves Arrows.Compatible for the indexed family. No choice
of a family on the image presieve, cover-membership conclusion, cocone endpoint
equality, or alpha formula for refined arrows is part of this lemma. An empty
T has a vacuously matching indexed family and b can be the identity; duplicates
are allowed and are included among the finitely many pairs.
-/
theorem colimit_site_abelian_finite_indexed_matching
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)))
    (t : Under i) (W : F.obj t.right) (T : Presieve W) (hT : T ∈ P t.right W)
    (y : T.FamilyOfElements
      (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
          forget AddCommGrpCat.{u}))
    (hy : (show T.FamilyOfElements
        ((V.ι.app t.right).toFunctor.op ⋙
          (ColimitSiteStageImage.target F P V Q i G).obj ⋙ forget AddCommGrpCat.{u}) from
        fun {Z} g hg ↦ (α t).hom.app (op Z) (y g hg)).Compatible) :
    ∃ (t' : Under i) (b : t ⟶ t'),
      Presieve.Arrows.Compatible
        (((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj ⋙
            forget AddCommGrpCat.{u})
        (fun s : T.uncurry ↦ (F.map b.right).toFunctor.map s.val.2)
        (fun s : T.uncurry ↦ (θ t t' b).hom.app (op s.val.1) (y s.val.2 s.property))
 := by
  classical
  let A (s : Under i) := (sheafPullback (F.map s.hom).toFunctor AddCommGrpCat.{u}
    (P i).toGrothendieck (P s.right).toGrothendieck).obj G
  have w {s s' : Under i} (b : s ⟶ s') :
      (F.map s.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map s'.hom).toFunctor := by
    change (F.map s.hom ≫ F.map b.right).toFunctor = _
    rw [← F.map_comp, Under.w b]
  have hstep (s s' : Under i) (b : t ⟶ s) (c : s ⟶ s')
      (X : F.obj t.right) (x z : (A t).obj.obj (op X))
      (hxz : (θ t s b).hom.app (op X) x = (θ t s b).hom.app (op X) z) :
      (θ t s' (b ≫ c)).hom.app (op X) x =
        (θ t s' (b ≫ c)).hom.app (op X) z := by
    have wc : (F.map b.right).toFunctor ⋙ (F.map c.right).toFunctor =
        (F.map (b ≫ c).right).toFunctor := by
      change (F.map b.right ≫ F.map c.right).toFunctor = _
      rw [← F.map_comp]
      rfl
    have hc := sheaf_comparison_comp (P i).toGrothendieck (P t.right).toGrothendieck
      (P s.right).toGrothendieck (P s'.right).toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map c.right).toFunctor
      (F.map s.hom).toFunctor (F.map s'.hom).toFunctor (F.map (b ≫ c).right).toFunctor
      (w b) (w c) wc G (A s) (A s')
      ((sheafAdjunctionContinuous (F.map s.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P s.right).toGrothendieck).unit.app G)
      ((sheafAdjunctionContinuous (F.map s'.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P s'.right).toGrothendieck).unit.app G)
      (θ t s b) (θ s s' c) (θ t s' (b ≫ c))
      (hθ t s b) (hθ s s' c) (hθ t s' (b ≫ c)) X
    apply (arrow_values_iff _ _ hc x z).mp
    exact congrArg ((θ s s' c).hom.app (op ((F.map b.right).toFunctor.obj X))) hxz
  have : Finite T.uncurry := hfinite t.right W T hT
  have : T.HasPairwisePullbacks := (P t.right).hasPairwisePullbacks_of_mem hT
  have hpair (s r : T.uncurry) : HasPullback s.val.2 r.val.2 :=
    Presieve.HasPairwisePullbacks.has_pullbacks s.property r.property
  let X (l : T.uncurry × T.uncurry) := pullback l.1.val.2 l.2.val.2
  let x (l : T.uncurry × T.uncurry) : (A t).obj.obj (op (X l)) :=
    (A t).obj.map (pullback.fst l.1.val.2 l.2.val.2).op (y l.1.val.2 l.1.property)
  let z (l : T.uncurry × T.uncurry) : (A t).obj.obj (op (X l)) :=
    (A t).obj.map (pullback.snd l.1.val.2 l.2.val.2).op (y l.2.val.2 l.2.property)
  obtain ⟨t', b, hb⟩ := finite_refinement t (T.uncurry × T.uncurry)
    (fun s b l ↦ (θ t s b).hom.app (op (X l)) (x l) =
      (θ t s b).hom.app (op (X l)) (z l))
    (fun s s' b c l ↦ hstep s s' b c (X l) (x l) (z l))
    (fun l ↦ colimit_site_abelian_pairwise_eventual_matching
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
      i G α θ hα hθ t W T hT y hy (X l) l.1 l.2
      (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
  refine ⟨t', b, ?_⟩
  intro s r Z gs gr heq
  let f := (F.map b.right).toFunctor
  have : PreservesLimit (cospan s.val.2 r.val.2) f :=
    hpullback t.right t'.right b.right W s.val.1 r.val.1 T hT
      s.val.2 r.val.2 s.property
  have hp := (IsPullback.of_hasPullback s.val.2 r.val.2).map f
  obtain ⟨l, hl₁, hl₂⟩ := hp.exists_lift gs gr heq
  have h₁ := ConcreteCategory.congr_hom
    ((θ t t' b).hom.naturality (pullback.fst s.val.2 r.val.2).op)
    (y s.val.2 s.property)
  have h₂ := ConcreteCategory.congr_hom
    ((θ t t' b).hom.naturality (pullback.snd s.val.2 r.val.2).op)
    (y r.val.2 r.property)
  have he : (A t').obj.map (f.map (pullback.fst s.val.2 r.val.2)).op
        ((θ t t' b).hom.app (op s.val.1) (y s.val.2 s.property)) =
      (A t').obj.map (f.map (pullback.snd s.val.2 r.val.2)).op
        ((θ t t' b).hom.app (op r.val.1) (y r.val.2 r.property)) :=
    h₁.symm.trans ((hb (s, r)).trans h₂)
  change (A t').obj.map gs.op _ = (A t').obj.map gr.op _
  rw [← hl₁, ← hl₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  exact congrArg ((A t').obj.map l.op) he


end CategoryTheory
