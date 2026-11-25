/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Unit-compatible section maps satisfy the functor and cocone laws.

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-section-coherence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem sheaf_unit_unique
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous T S]
    (G : Sheaf T (Type u)) (H : Sheaf S (Type u))
    (a b : (sheafPullback f (Type u) T S).obj G ⟶ H)
    (h : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
        (op X) ≫ b.hom.app (op (f.obj X)))) : a = b := by
  apply ((sheafAdjunctionContinuous f (Type u) T S).homEquiv G H).injective
  ext1
  apply NatTrans.ext
  funext X
  exact (Arrow.mk_inj _ _).mp (h (unop X))

private theorem sheaf_triangle_comp
    {C D E Z : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory E] [SmallCategory Z]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (Q : GrothendieckTopology Z)
    (f : C ⥤ D) (g : D ⥤ E) (k : E ⥤ Z)
    (h : C ⥤ E) (l : C ⥤ Z) (m : D ⥤ Z)
    [f.IsContinuous T S] [g.IsContinuous S R] [k.IsContinuous R Q]
    [h.IsContinuous T R] [l.IsContinuous T Q] [m.IsContinuous S Q]
    (w₁ : f ⋙ g = h) (w₂ : h ⋙ k = l) (w₃ : g ⋙ k = m)
    (G : Sheaf T (Type u))
    (a : (sheafPullback f (Type u) T S).obj G ⟶
      (g.sheafPushforwardContinuous (Type u) S R).obj
        ((sheafPullback h (Type u) T R).obj G))
    (b : (sheafPullback h (Type u) T R).obj G ⟶
      (k.sheafPushforwardContinuous (Type u) R Q).obj
        ((sheafPullback l (Type u) T Q).obj G))
    (c : (sheafPullback f (Type u) T S).obj G ⟶
      (m.sheafPushforwardContinuous (Type u) S Q).obj
        ((sheafPullback l (Type u) T Q).obj G))
    (ha : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous h (Type u) T R).unit.app G).hom.app
        (op X)))
    (hb : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous h (Type u) T R).unit.app G).hom.app
        (op X) ≫ b.hom.app (op (h.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous l (Type u) T Q).unit.app G).hom.app
        (op X)))
    (hc : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
        (op X) ≫ c.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous l (Type u) T Q).unit.app G).hom.app
        (op X))) (Y : D) :
    Arrow.mk (a.hom.app (op Y) ≫ b.hom.app (op (g.obj Y))) =
      Arrow.mk (c.hom.app (op Y)) := by
  subst h
  subst l
  subst m
  have eq : a ≫ (g.sheafPushforwardContinuous (Type u) S R).map b = c := by
    apply sheaf_unit_unique T S f G _
    intro X
    change Arrow.mk
      (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app (op X) ≫
        (a.hom.app (op (f.obj X)) ≫ b.hom.app (op (g.obj (f.obj X))))) = _
    rw [← Category.assoc, (Arrow.mk_inj _ _).mp (ha X)]
    exact (hb X).trans (hc X).symm
  exact congrArg (fun z ↦ Arrow.mk (z.hom.app (op Y))) eq

private theorem sheaf_triangle_id
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (f : C ⥤ D) (g : D ⥤ D)
    [f.IsContinuous T S] [g.IsContinuous S S]
    (w : g = 𝟭 D) (G : Sheaf T (Type u))
    (a : (sheafPullback f (Type u) T S).obj G ⟶
      (g.sheafPushforwardContinuous (Type u) S S).obj
        ((sheafPullback f (Type u) T S).obj G))
    (ha : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
        (op X))) (Y : D) :
    Arrow.mk (a.hom.app (op Y)) =
      Arrow.mk (𝟙 (((sheafPullback f (Type u) T S).obj G).obj.obj (op Y))) := by
  subst g
  let b : (sheafPullback f (Type u) T S).obj G ⟶
      ((𝟭 D).sheafPushforwardContinuous (Type u) S S).obj
        ((sheafPullback f (Type u) T S).obj G) := ⟨𝟙 _⟩
  have eq : a = b := by
    apply sheaf_unit_unique T S f G _
    intro X
    change Arrow.mk (_ ≫ a.hom.app (op (f.obj X))) = Arrow.mk (_ ≫ 𝟙 _)
    rw [Category.comp_id]
    exact ha X
  simpa [b] using congrArg (fun z ↦ Arrow.mk (z.hom.app (op Y))) eq


-- The arrow binder in the given family m does not occur in its codomain.
set_option linter.unusedVariables false in
/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-set-section-coherence).

Unit-compatible section maps satisfy the functor and cocone laws.

Proof: The equalities of functors supplied by F.map_id, F.map_comp, Under.w,
and V.w identify all composite restriction functors. For each transition, the
adjunction hom equivalence sends a sheaf map to its composite with the unit.
Consequently the componentwise unit equations hθ determine the transition
uniquely: equality of components gives equality of natural transformations,
and injectivity of the hom equivalence gives equality of sheaf maps. The
identity sheaf map satisfies the identity unit equation. A composite of two
transitions satisfies the composite unit equation, by naturality of the units
and of the second transition. Uniqueness therefore proves identity and
composition. Likewise, the composite of a transition with the later α has
unit composite equal to the limit-site unit by hθ and hα, so equals the earlier
α. Evaluate these three sheaf-map equalities at the image of U. The Arrow
identities hm and hc identify m and c with these evaluated maps, after the
endpoint transports forced by the functor equalities. Transport respects
identities and composition, giving the three stated laws. No filteredness,
covering finiteness, or category-colimit hypothesis is needed.
-/
theorem colimit_site_set_section_coherence
    (J : Type u) [SmallCategory J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G))
    (hα : (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))))
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
    (U : F.obj i)
    (m : ∀ (t t' : Under i) (b : t ⟶ t'), ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)) ⟶ ((sheafPullback (F.map t'.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t'.hom).toFunctor.obj U)))
    (c : ∀ t : Under i, ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)) ⟶ ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
          (op ((V.ι.app i).toFunctor.obj U)))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk (m t t' b) =
        Arrow.mk ((θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))))
    (hc : ∀ t : Under i,
      Arrow.mk (c t) =
        Arrow.mk ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) :
    (∀ t : Under i, m t t (𝟙 t) = 𝟙 _) ∧
    (∀ (t t' t'' : Under i) (b : t ⟶ t') (b' : t' ⟶ t''),
      m t t'' (b ≫ b') = m t t' b ≫ m t' t'' b') ∧
    (∀ (t t' : Under i) (b : t ⟶ t'), m t t' b ≫ c t' = c t) := by
  classical
  let L (t : Under i) :=
    (sheafPullback (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  let W (t : Under i) (X : F.obj i) := (F.map t.hom).toFunctor.obj X
  have w {t t' : Under i} (b : t ⟶ t') :
      (F.map t.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map t'.hom).toFunctor := by
    change (F.map t.hom ≫ F.map b.right).toFunctor = _
    rw [← F.map_comp, Under.w b]
  have hv (t : Under i) :
      (F.map t.hom).toFunctor ⋙ (V.ι.app t.right).toFunctor =
        (V.ι.app i).toFunctor :=
    congrArg Cat.Hom.toFunctor (V.w t.hom)
  have hid (t : Under i) (Y : F.obj t.right) :
      Arrow.mk ((θ t t (𝟙 t)).hom.app (op Y)) = Arrow.mk (𝟙 ((L t).obj.obj (op Y))) := by
    exact sheaf_triangle_id (P i).toGrothendieck (P t.right).toGrothendieck
      (F.map t.hom).toFunctor (F.map (Under.Hom.right (𝟙 t))).toFunctor
      (by change (F.map (𝟙 t.right)).toFunctor = _; simp) G (θ t t (𝟙 t))
      (hθ t t (𝟙 t)) Y
  have hcomp (t t' t'' : Under i) (b : t ⟶ t') (c : t' ⟶ t'')
      (Y : F.obj t.right) :
      Arrow.mk ((θ t t' b).hom.app (op Y) ≫
        (θ t' t'' c).hom.app (op ((F.map b.right).toFunctor.obj Y))) =
      Arrow.mk ((θ t t'' (b ≫ c)).hom.app (op Y)) := by
    apply sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck (P t''.right).toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map c.right).toFunctor
      (F.map t'.hom).toFunctor (F.map t''.hom).toFunctor
      (F.map (b ≫ c).right).toFunctor (w b) (w c) _ G
      (θ t t' b) (θ t' t'' c) (θ t t'' (b ≫ c))
      (hθ t t' b) (hθ t' t'' c) (hθ t t'' (b ≫ c)) Y
    change (F.map b.right ≫ F.map c.right).toFunctor = _
    rw [← F.map_comp]
    rfl
  have hcone (t t' : Under i) (b : t ⟶ t') (Y : F.obj t.right) :
      Arrow.mk ((θ t t' b).hom.app (op Y) ≫
        (α t').hom.app (op ((F.map b.right).toFunctor.obj Y))) =
      Arrow.mk ((α t).hom.app (op Y)) := by
    exact sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck Q.toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (V.ι.app t'.right).toFunctor
      (F.map t'.hom).toFunctor (V.ι.app i).toFunctor (V.ι.app t.right).toFunctor
      (w b) (hv t') (congrArg Cat.Hom.toFunctor (V.w b.right)) G
      (θ t t' b) (α t') (α t) (hθ t t' b) (hα t') (hα t) Y
  have hw {t t' : Under i} (b : t ⟶ t') (X : F.obj i) :
      (F.map b.right).toFunctor.obj (W t X) = W t' X :=
    congrArg (fun f ↦ f.obj X) (w b)
  have hvo (t : Under i) (X : F.obj i) :
      (V.ι.app t.right).toFunctor.obj (W t X) = (V.ι.app i).toFunctor.obj X :=
    congrArg (fun f ↦ f.obj X) (hv t)
  let A (t : Under i) := (L t).obj.obj (op (W t U))
  let mm {t t' : Under i} (b : t ⟶ t') : A t ⟶ A t' :=
    (θ t t' b).hom.app (op (W t U)) ≫
      eqToHom (congrArg (fun Y ↦ (L t').obj.obj (op Y)) (hw b U))
  have hmm_id (t : Under i) : mm (𝟙 t) = 𝟙 (A t) := by
    apply (Arrow.mk_injective _ _)
    simpa only [mm, Arrow.arrow_mk_comp_eqToHom] using hid t (W t U)
  have hmm_comp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
      mm (b ≫ c) = mm b ≫ mm c := by
    apply (Arrow.mk_injective _ _)
    have hn := (θ t' t'' c).hom.naturality (eqToHom (congrArg op (hw b U)))
    simp only [eqToHom_map] at hn
    calc
      Arrow.mk (mm (b ≫ c)) = Arrow.mk ((θ t t'' (b ≫ c)).hom.app (op (W t U))) := by
        simp only [mm, Arrow.arrow_mk_comp_eqToHom]
      _ = Arrow.mk ((θ t t' b).hom.app (op (W t U)) ≫
          (θ t' t'' c).hom.app (op ((F.map b.right).toFunctor.obj (W t U)))) :=
        (hcomp t t' t'' b c (W t U)).symm
      _ = Arrow.mk (mm b ≫ mm c) := by
        dsimp only [mm]
        rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
  let H := (sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let k (t : Under i) : A t ⟶ H.obj.obj (op ((V.ι.app i).toFunctor.obj U)) :=
    (α t).hom.app (op (W t U)) ≫
      eqToHom (congrArg (fun Y ↦ H.obj.obj (op Y)) (hvo t U))
  have hk {t t' : Under i} (b : t ⟶ t') : mm b ≫ k t' = k t := by
    apply (Arrow.mk_injective _ _)
    have hn := (α t').hom.naturality (eqToHom (congrArg op (hw b U)))
    simp only [eqToHom_map] at hn
    calc
      Arrow.mk (mm b ≫ k t') =
          Arrow.mk ((θ t t' b).hom.app (op (W t U)) ≫
            (α t').hom.app (op ((F.map b.right).toFunctor.obj (W t U)))) := by
        dsimp only [mm, k]
        rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
      _ = Arrow.mk ((α t).hom.app (op (W t U))) := hcone t t' b (W t U)
      _ = Arrow.mk (k t) := by simp only [k, Arrow.arrow_mk_comp_eqToHom]
  have hm' (t t' : Under i) (b : t ⟶ t') : m t t' b = mm b := by
    apply Arrow.mk_injective
    exact (hm t t' b).trans (by simp only [mm, W, Arrow.arrow_mk_comp_eqToHom])
  have hc' (t : Under i) : c t = k t := by
    apply Arrow.mk_injective
    exact (hc t).trans (by simp only [k, W, Arrow.arrow_mk_comp_eqToHom])
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [hm']
    exact hmm_id t
  · intro t t' t'' b b'
    simp only [hm']
    exact hmm_comp b b'
  · intro t t' b
    rw [hm', hc', hc']
    exact hk b

end CategoryTheory
