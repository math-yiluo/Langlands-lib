/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Construct the section diagram from transition maps satisfying the unit equation.
Source: Stacks Project, Sites, Tag 0A35, section formula and adjunction paragraph.
(blueprint: lem-weil-pbc-stage-section-functor-from-transitions).

Proof: Write S_t for inverse image along f_t = F(t.hom), R_t for restriction,
and eta_t for its unit. For each b : t to t', the hypothesis at every X is the
sheaf equation eta_t(G) followed by R_t(theta_b(G)) = eta_t'(G), after identifying
iterated restriction using F.map_comp and Under.w. Equality of Arrow objects
retains precisely this identification of endpoints. The adjunction hom-set
bijection at t is injective, so this equation determines theta_b(G) uniquely.
For an identity refinement, the identity on S_t(G), transported along F.map_id,
satisfies that equation; therefore theta_id is that identity. For composable
b and c, theta_b followed by restriction of theta_c satisfies the equation
for c composed with b: apply the unit equation for b and then for c.
Functoriality of precomposition identifies the iterated restrictions, with
transports along F.map_comp. Injectivity gives the composition law.

Set L(G)(t) = S_t(G)(f_t(U)). Define L(G)(b) by evaluating theta_b(G) at f_t(U),
then transporting from S_t'(G)(F(b.right)(f_t(U))) to S_t'(G)(f_t'(U)). The laws
just established, together with cancellation of equality transports, give
map_id and map_comp. For a sheaf morphism G to H, evaluate S_t on that morphism
at f_t(U); naturality of theta makes these components a map of diagrams.
Functoriality of each S_t gives the identity and composition laws in G, hence
L is a functor. Its evaluation at t has the stated object and morphism maps,
so the identity identifications give E_t. Unfolding L(G)(b) and cancelling the
endpoint transport gives the final Arrow equality. This construction uses the
given theta; it does not choose transition maps from a mere existence theorem.
-/
theorem stage_section_functor_from_transitions
    (J : Type u) [SmallCategory J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (i : J) (U : F.obj i)
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
        sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⟶
        sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck ⋙
          (F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
            (P t.right).toGrothendieck (P t'.right).toGrothendieck)
    (hθ : ∀ (G : Sheaf (P i).toGrothendieck (Type u))
        (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
        Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
            (op X) ≫ ((θ t t' b).app G).hom.app
              (op ((F.map t.hom).toFunctor.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app
            (op X))) :
    ∃ (L : Sheaf (P i).toGrothendieck (Type u) ⥤ (Under i ⥤ Type u))
      (E : ∀ t : Under i, L ⋙ (evaluation (Under i) (Type u)).obj t ≅
        sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⋙
          sheafToPresheaf (P t.right).toGrothendieck (Type u) ⋙
          (evaluation (F.obj t.right)ᵒᵖ (Type u)).obj
            (op ((F.map t.hom).toFunctor.obj U))),
      ∀ (G : Sheaf (P i).toGrothendieck (Type u))
        (t t' : Under i) (b : t ⟶ t'),
        Arrow.mk ((E t).hom.app G ≫ ((θ t t' b).app G).hom.app
          (op ((F.map t.hom).toFunctor.obj U))) =
        Arrow.mk ((L.obj G).map b ≫ (E t').hom.app G) := by
  have sheaf_unit_unique
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
  -- Two compatible triangles compose to the triangle for the composite.
  have sheaf_triangle_comp
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
  -- The identity also satisfies the unit equation.
  have sheaf_triangle_id
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
  -- Evaluate the coherent triangles to obtain diagrams and their maps.
  let S := fun t : Under i => sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck
  let W := fun (t : Under i) (X : F.obj i) => (F.map t.hom).toFunctor.obj X
  have hw {t t' : Under i} (b : t ⟶ t') (X : F.obj i) :
      (F.map b.right).toFunctor.obj (W t X) = W t' X := by
    have hf : (F.map t.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map t'.hom).toFunctor := by
      change (F.map t.hom ≫ F.map b.right).toFunctor = _
      rw [← F.map_comp, Under.w b]
    exact congrArg (fun f ↦ f.obj X) hf
  let D (G : Sheaf (P i).toGrothendieck (Type u)) : Under i ⥤ Type u := by
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
    have hw {t t' : Under i} (b : t ⟶ t') (X : F.obj i) :
        (F.map b.right).toFunctor.obj (W t X) = W t' X :=
      congrArg (fun f ↦ f.obj X) (w b)
    have hid (t : Under i) (Y : F.obj t.right) :
        Arrow.mk (((θ t t (𝟙 t)).app G).hom.app (op Y)) = Arrow.mk (𝟙 ((L t).obj.obj (op Y))) := by
      exact sheaf_triangle_id (P i).toGrothendieck (P t.right).toGrothendieck
        (F.map t.hom).toFunctor (F.map (Under.Hom.right (𝟙 t))).toFunctor
        (by change (F.map (𝟙 t.right)).toFunctor = _; simp) G ((θ t t (𝟙 t)).app G)
        (hθ G t t (𝟙 t)) Y
    have hcomp (t t' t'' : Under i) (b : t ⟶ t') (c : t' ⟶ t'')
        (Y : F.obj t.right) :
        Arrow.mk (((θ t t' b).app G).hom.app (op Y) ≫
          ((θ t' t'' c).app G).hom.app (op ((F.map b.right).toFunctor.obj Y))) =
        Arrow.mk (((θ t t'' (b ≫ c)).app G).hom.app (op Y)) := by
      apply sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
        (P t'.right).toGrothendieck (P t''.right).toGrothendieck
        (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map c.right).toFunctor
        (F.map t'.hom).toFunctor (F.map t''.hom).toFunctor
        (F.map (b ≫ c).right).toFunctor (w b) (w c) _ G
        ((θ t t' b).app G) ((θ t' t'' c).app G) ((θ t t'' (b ≫ c)).app G)
        (hθ G t t' b) (hθ G t' t'' c) (hθ G t t'' (b ≫ c)) Y
      change (F.map b.right ≫ F.map c.right).toFunctor = _
      rw [← F.map_comp]
      rfl
    let A (t : Under i) := (L t).obj.obj (op (W t U))
    let m {t t' : Under i} (b : t ⟶ t') : A t ⟶ A t' :=
      ((θ t t' b).app G).hom.app (op (W t U)) ≫
        eqToHom (congrArg (fun Y ↦ (L t').obj.obj (op Y)) (hw b U))
    have hm_id (t : Under i) : m (𝟙 t) = 𝟙 (A t) := by
      apply (Arrow.mk_injective _ _)
      simpa only [m, Arrow.arrow_mk_comp_eqToHom] using hid t (W t U)
    have hm_comp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
        m (b ≫ c) = m b ≫ m c := by
      apply (Arrow.mk_injective _ _)
      have hn := ((θ t' t'' c).app G).hom.naturality (eqToHom (congrArg op (hw b U)))
      simp only [eqToHom_map] at hn
      calc
        Arrow.mk (m (b ≫ c)) = Arrow.mk (((θ t t'' (b ≫ c)).app G).hom.app (op (W t U))) := by
          simp only [m, Arrow.arrow_mk_comp_eqToHom]
        _ = Arrow.mk (((θ t t' b).app G).hom.app (op (W t U)) ≫
            ((θ t' t'' c).app G).hom.app (op ((F.map b.right).toFunctor.obj (W t U)))) :=
          (hcomp t t' t'' b c (W t U)).symm
        _ = Arrow.mk (m b ≫ m c) := by
          dsimp only [m]
          rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
          simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    exact
      { obj := A
        map := fun b ↦ m b
        map_id := hm_id
        map_comp := fun b c ↦ hm_comp b c }
  let L : Sheaf (P i).toGrothendieck (Type u) ⥤ (Under i ⥤ Type u) :=
    { obj := D
      map := fun {G H} f =>
        { app := fun t => ((S t).map f).hom.app (op (W t U))
          naturality := by
            intro t t' b
            have hn := congrArg (fun z => z.hom.app (op (W t U)))
              ((θ t t' b).naturality f)
            change ((S t).map f).hom.app (op (W t U)) ≫
              ((θ t t' b).app H).hom.app (op (W t U)) =
              ((θ t t' b).app G).hom.app (op (W t U)) ≫
                ((S t').map f).hom.app (op ((F.map b.right).toFunctor.obj (W t U))) at hn
            have hv := ((S t').map f).hom.naturality
              (eqToHom (congrArg op (hw b U)))
            simp only [eqToHom_map] at hv
            change (((θ t t' b).app G).hom.app (op (W t U)) ≫ eqToHom _) ≫
              ((S t').map f).hom.app (op (W t' U)) =
              ((S t).map f).hom.app (op (W t U)) ≫
                (((θ t t' b).app H).hom.app (op (W t U)) ≫ eqToHom _)
            rw [Category.assoc, hv, ← Category.assoc, ← hn, Category.assoc] }
      map_id := by
        intro G
        apply NatTrans.ext
        funext t
        change ((S t).map (𝟙 G)).hom.app (op (W t U)) = 𝟙 _
        simp
      map_comp := by
        intro G H K f g
        apply NatTrans.ext
        funext t
        change ((S t).map (f ≫ g)).hom.app (op (W t U)) = _
        simp }
  refine ⟨L, fun t => Iso.refl _, ?_⟩
  intro G t t' b
  change Arrow.mk (𝟙 _ ≫ ((θ t t' b).app G).hom.app (op (W t U))) =
    Arrow.mk (_ ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  change Arrow.mk (((θ t t' b).app G).hom.app (op (W t U))) =
    Arrow.mk (((θ t t' b).app G).hom.app (op (W t U)) ≫ eqToHom _)
  exact (Arrow.arrow_mk_comp_eqToHom _ _).symm

end CategoryTheory
