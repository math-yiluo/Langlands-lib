/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.CategoryTheory.ColimitSiteRawFiniteEqualityStabilization
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma

/-! # Finite raw overlap refinement

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-matching-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem raw_arrow_transport {C : Type u} [Category.{u} C]
    (H : Cᵒᵖ ⥤ Type u) {X Y : C} (e : X = Y) {S : Type u}
    (a : S ⟶ H.obj (op Y)) (b : S ⟶ H.obj (op X))
    (h : Arrow.mk a = Arrow.mk b) : b = a ≫ H.map (eqToHom e).op := by
  subst Y
  obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff a b).mp h
  simpa using hh.symm

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
the finite overlap-equation calculation before stage gluing.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-matching-refinement).

Proof: Take the pairwise covering pullbacks at the given stage. Naturality of beta
and the coprojections identifies the raw images of the two restricted sections.
The assumed raw compatibility makes them equal. The pointwise Kan presentation,
with object and arrow set colimits, detects equality of stage sections after a
transition: lift the finite chain of Kan and outer colimit relations to one stage,
where naturality and h-beta-map turn them into restriction and theta transport.
The unit condition h-theta makes theta the unique adjunction transpose and hence
makes these transports compose. There are finitely many pairs of covering arrows;
filteredness and equalization give one transition where every equality holds.
Transition preservation of covering pullbacks identifies the transported equations
with equations on pairwise pullbacks at the new stage. The pullback universal
property proves indexed compatibility on arbitrary common test objects. Transport
the original sections by theta to obtain s'. Naturality and h-beta-map give the
stated equality of raw images; e is the cocone equality. Repeated arrows therefore
have equal sections, including after transport. For an empty family use the identity
transition and the empty family. No new raw representatives or amalgamation are needed.
-/
theorem colimit_site_raw_finite_matching_refinement
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasPullbacks]
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
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (t : Under i) (W : F.obj t.right) (I : Type u) [Finite I]
    (Y : I → F.obj t.right) (f : ∀ p, Y p ⟶ W)
    (hf : Presieve.ofArrows Y f ∈ P t.right W)
    (s : ∀ p, ((sheafPullback (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op (Y p)))
    (hs : Presieve.Arrows.Compatible ((V.ι.app t.right).toFunctor.op ⋙ colimit B) f
      (fun p ↦ (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (Y p)))
        ((β t).app (op (Y p)) (s p)))) :
    ∃ (t' : Under i) (b : t ⟶ t')
      (e : ∀ U : F.obj t.right,
        (V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj U) =
          (V.ι.app t.right).toFunctor.obj U)
      (s' : ∀ p, ((sheafPullback (F.map t'.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.obj
          (op ((F.map b.right).toFunctor.obj (Y p)))),
      Presieve.Arrows.Compatible
        ((sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj
        (fun p ↦ (F.map b.right).toFunctor.map (f p)) s' ∧
      ∀ p, (colimit.ι B t').app
        (op ((V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj (Y p))))
        ((β t').app (op ((F.map b.right).toFunctor.obj (Y p))) (s' p)) =
      (colimit B).map (eqToHom (e (Y p))).op
        ((colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (Y p)))
          ((β t).app (op (Y p)) (s p))) := by
  classical
  clear hcover
  let A : ∀ v : Under i, (F.obj v.right)ᵒᵖ ⥤ Type u := fun v ↦
    ((sheafPullback (F.map v.hom).toFunctor (Type u)
      (P i).toGrothendieck (P v.right).toGrothendieck).obj G).obj
  let ρ : A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ colimit B :=
    β t ≫ Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
  let : (Presieve.ofArrows Y f).HasPairwisePullbacks :=
    (P t.right).hasPairwisePullbacks_of_mem hf
  let X : I × I → F.obj t.right := fun p ↦ pullback (f p.1) (f p.2)
  let r : ∀ p, (A t).obj (op (X p)) := fun p ↦
    (A t).map (pullback.fst (f p.1) (f p.2)).op (s p.1)
  let z : ∀ p, (A t).obj (op (X p)) := fun p ↦
    (A t).map (pullback.snd (f p.1) (f p.2)).op (s p.2)
  have hsρ : Presieve.Arrows.Compatible
      ((V.ι.app t.right).toFunctor.op ⋙ colimit B) f
      (fun p ↦ ρ.app (op (Y p)) (s p)) := by
    simpa [ρ, NatTrans.comp_app, Functor.whiskerLeft] using hs
  have hrz : ∀ p, ρ.app (op (X p)) (r p) = ρ.app (op (X p)) (z p) := by
    intro p
    have h₁ := congrArg (fun k ↦ k (s p.1))
      (ρ.naturality (pullback.fst (f p.1) (f p.2)).op)
    have h₂ := congrArg (fun k ↦ k (s p.2))
      (ρ.naturality (pullback.snd (f p.1) (f p.2)).op)
    simp only [types_comp_apply] at h₁ h₂
    exact h₁.trans ((hsρ p.1 p.2 _ _ _ pullback.condition).trans h₂.symm)
  obtain ⟨t', b, hb⟩ := colimit_site_raw_finite_equality_stabilization
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap t (I × I) X r z
      (by simpa [ρ, NatTrans.comp_app, Functor.whiskerLeft] using hrz)
  let T := (F.map b.right).toFunctor
  let s' : ∀ p, (A t').obj (op (T.obj (Y p))) := fun p ↦
    (θ t t' b).hom.app (op (Y p)) (s p)
  have he : ∀ U : F.obj t.right,
      (V.ι.app t'.right).toFunctor.obj (T.obj U) =
        (V.ι.app t.right).toFunctor.obj U := by
    intro U
    exact congrArg (fun c : F.obj t.right ⟶ V.pt ↦ c.toFunctor.obj U)
      (V.w b.right)
  refine ⟨t', b, he, s', ?_, ?_⟩
  · intro p q Z gp gq hpq
    let : PreservesLimit (cospan (f p) (f q)) T :=
      hpullback t.right t'.right b.right W (Y p) (Y q)
        (Presieve.ofArrows Y f) hf (f p) (f q) (Presieve.ofArrows.mk p)
    let L := isLimitOfHasPullbackOfPreservesLimit T (f p) (f q)
    let l := PullbackCone.IsLimit.lift L gp gq hpq
    have h₁ := congrArg (fun k ↦ k (s p))
      ((θ t t' b).hom.naturality (pullback.fst (f p) (f q)).op)
    have h₂ := congrArg (fun k ↦ k (s q))
      ((θ t t' b).hom.naturality (pullback.snd (f p) (f q)).op)
    have hx : (A t').map (T.map (pullback.fst (f p) (f q))).op (s' p) =
        (A t').map (T.map (pullback.snd (f p) (f q))).op (s' q) :=
      h₁.symm.trans ((hb (p, q)).trans h₂)
    have hl₁ : l ≫ T.map (pullback.fst (f p) (f q)) = gp :=
      PullbackCone.IsLimit.lift_fst L gp gq hpq
    have hl₂ : l ≫ T.map (pullback.snd (f p) (f q)) = gq :=
      PullbackCone.IsLimit.lift_snd L gp gq hpq
    rw [← hl₁, ← hl₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    exact congrArg (fun a ↦ (A t').map l.op a) hx
  · intro p
    have hβeq := raw_arrow_transport (B.obj t') (he (Y p))
      ((β t).app (op (Y p)) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj (Y p))))
      ((θ t t' b).hom.app (op (Y p)) ≫
        (β t').app (op (T.obj (Y p)))) (hβmap t t' b (Y p))
    have hn := (colimit.ι B t').naturality (eqToHom (he (Y p))).op
    have hw := congrArg
      (fun τ ↦ τ.app (op ((V.ι.app t.right).toFunctor.obj (Y p)))) (colimit.w B b)
    simp only [NatTrans.comp_app] at hw
    change (((θ t t' b).hom.app (op (Y p)) ≫
      (β t').app (op (T.obj (Y p)))) ≫
      (colimit.ι B t').app (op ((V.ι.app t'.right).toFunctor.obj (T.obj (Y p)))))
        (s p) = _
    rw [hβeq, Category.assoc, hn, ← Category.assoc]
    rw [Category.assoc ((β t).app (op (Y p))), hw]
    rfl

end CategoryTheory
