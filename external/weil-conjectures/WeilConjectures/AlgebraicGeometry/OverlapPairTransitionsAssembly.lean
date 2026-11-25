/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-! # Assemble natural transitions from maps on universal pairwise overlaps

Source: Stacks Project, Tag 01ZR, first proof, Zariski gluing and pullback.
(blueprint: lem-pc-overlap-pair-transitions-assembly). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

/-- Extend maps on universal pairwise overlaps to all test objects.
The construction uses only pullback lifts and pseudofunctor composition.
(blueprint: lem-pc-overlap-pair-transitions-assembly). -/
private noncomputable def overlapTransitionsOfPairs
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {ι : Type u} {S : C} {X : ι → C}
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1}) (f : ∀ a, X a ⟶ S)
    (N : ∀ a, F.obj (.mk (op (X a))))
    (φ : ∀ a b, (F.map (pullback.fst (f a) (f b)).op.toLoc).toFunctor.obj (N a) ⟶
      (F.map (pullback.snd (f a) (f b)).op.toLoc).toFunctor.obj (N b)) :
    F.OverlapTransitions f where
  obj := N
  hom _ q a b f₁ f₂ hf₁ hf₂ :=
    pullHom (φ a b) (pullback.lift f₁ f₂ (hf₁.trans hf₂.symm)) f₁ f₂
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  pullHom_hom _ _ g _ _ _ a b f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullHom_pullHom]
    have he : g ≫ pullback.lift f₁ f₂ (hf₁.trans hf₂.symm) =
        pullback.lift gf₁ gf₂ (by rw [← hgf₁, ← hgf₂, Category.assoc,
          Category.assoc, hf₁, hf₂]) := by
      apply pullback.hom_ext <;> simp [Category.assoc, hgf₁, hgf₂]
    simp only [he]

/-- The universal-overlap value of pulled pair transitions is the base-change formula.
(blueprint: lem-pc-overlap-pair-transitions-assembly). -/
private lemma overlapTransitionsOfPairs_pull_hom
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {ι : Type u} {S S' : C} {X X' : ι → C}
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    (f : ∀ a, X a ⟶ S) (f' : ∀ a, X' a ⟶ S')
    (p : S' ⟶ S) (p' : ∀ a, X' a ⟶ X a)
    (w : ∀ a, p' a ≫ f a = f' a ≫ p)
    (N : ∀ a, F.obj (.mk (op (X a))))
    (φ : ∀ a b, (F.map (pullback.fst (f a) (f b)).op.toLoc).toFunctor.obj (N a) ⟶
      (F.map (pullback.snd (f a) (f b)).op.toLoc).toFunctor.obj (N b)) (a b : ι) :
    ((F.overlapTransitionsOfPairs f N φ).pull
      (f' := f') (p' := p') (p := p) (α := fun a ↦ a) w).hom
        (pullback.fst (f' a) (f' b) ≫ f' a)
        (pullback.fst _ _) (pullback.snd _ _) rfl pullback.condition.symm =
      F.overlapPairBaseChangeHom (f a) (f b) p (p' a) (p' b) (f' a) (f' b)
        (w a) (w b) (N a) (N b) (φ a b) := by
  rfl


open LocallyDiscreteOpToCat in
private noncomputable def overlapSquares {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {ι : Type u} {S : C} {X : ι → C}
    (f : ∀ a, X a ⟶ S)
    (a b : ι) : ChosenPullback (f a) (f b) where
  pullback := pullback (f a) (f b)
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := (IsPullback.of_hasPullback (f a) (f b)).isLimit

open LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_of_pairs {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {ι : Type u} {S : C} {X : ι → C}
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1}) (f : ∀ a, X a ⟶ S)
    (T : F.OverlapTransitions f) (D : F.DescentData f) (e : ∀ a, T.obj a ≅ D.obj a)
    (h : ∀ a b,
      (F.map (pullback.fst (f a) (f b)).op.toLoc).toFunctor.map (e a).hom ≫
          D.hom (pullback.fst (f a) (f b) ≫ f a)
            (pullback.fst _ _) (pullback.snd _ _) rfl pullback.condition.symm =
        T.hom (pullback.fst (f a) (f b) ≫ f a)
            (pullback.fst _ _) (pullback.snd _ _) rfl pullback.condition.symm ≫
          (F.map (pullback.snd (f a) (f b)).op.toLoc).toFunctor.map (e b).hom) :
    Nonempty (T.Comparison D) := by
  refine ⟨{ e := e, comm := ?_ }⟩
  intro Y q a b f₁ f₂ hf₁ hf₂
  let sq := overlapSquares f a b
  obtain ⟨p, hp₁, hp₂⟩ := sq.isPullback.exists_lift f₁ f₂ (hf₁.trans hf₂.symm)
  have hp : p ≫ sq.p = q := by rw [← sq.hp₁, ← Category.assoc, hp₁, hf₁]
  have hab : (F.map sq.p₁.op.toLoc).toFunctor.map (e a).hom ≫
      D.hom sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ =
    T.hom sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ ≫
      (F.map sq.p₂.op.toLoc).toFunctor.map (e b).hom := h a b
  rw [← D.pullHom_hom p sq.p q hp sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ f₁ f₂ hp₁ hp₂,
    ← T.pullHom_hom p sq.p q hp sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ f₁ f₂ hp₁ hp₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, hab, Functor.map_comp_assoc, mapComp'_inv_naturality]
  simp only [Category.assoc]

open LocallyDiscreteOpToCat in
private theorem assemblePairs
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    {ι : Type u} {S S' : C} {X X' : ι → C}
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    (f : ∀ a, X a ⟶ S) (f' : ∀ a, X' a ⟶ S')
    (p : S' ⟶ S) (p' : ∀ a, X' a ⟶ X a)
    (w : ∀ a, p' a ≫ f a = f' a ≫ p)
    (N : ∀ a, F.obj (.mk (op (X a)))) (D : F.DescentData f')
    (e : ∀ a, (F.map (p' a).op.toLoc).toFunctor.obj (N a) ≅ D.obj a)
    (φ : ∀ a b, (F.map (pullback.fst (f a) (f b)).op.toLoc).toFunctor.obj (N a) ⟶
      (F.map (pullback.snd (f a) (f b)).op.toLoc).toFunctor.obj (N b))
    (h : ∀ a b, F.overlapPairBaseChangeSquare f f' p p' w N D e a b (φ a b)) :
    ∃ T : F.OverlapTransitions f, (∀ a, T.obj a = N a) ∧
      Nonempty ((T.pull (f' := f') (p' := p') (p := p) (α := fun a ↦ a) w).Comparison D) := by
  let T := F.overlapTransitionsOfPairs f N φ
  refine ⟨T, (fun a ↦ rfl), ?_⟩
  apply comparison_of_pairs F f' (T.pull w) D e
  intro a b
  rw [overlapTransitionsOfPairs_pull_hom]
  exact h a b

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

/-- Maps on universal overlaps and their limit squares assemble into a natural comparison.
Source: Stacks Project, Tag 01ZR, first proof, after gluing the pairwise maps.
(blueprint: lem-pc-overlap-pair-transitions-assembly).

Proof: Set T.obj a = N a. For a test scheme Y with arrows f1 and f2 to the two
charts over the same q, use the universal map Y -> U_a ×_X U_b. Pull phi a b back
along it, and conjugate by the pseudofunctor composition comparisons; this is
the pseudofunctor pullHom formula. For g:Y' -> Y, the composite of g and the first universal
map equals the universal map associated to g f1 and g f2 by the two projection
equations. The pseudofunctor identity pullHom_pullHom proves naturality.
Thus T is an OverlapTransitions, with the prescribed objects literally equal.
At the limit its map on the universal overlap of U×_X Y is overlapPairPullHom.
Use the given e as the component isomorphisms. For arbitrary test arrows into
the limit charts, factor through their universal pairwise overlap and pull back
the assumed square. Naturality of both transition families and of mapComp'
makes the pulled-back square the required Comparison.comm equation. This does
not impose any identity or cocycle equation at the original stage. Neither
finiteness, finite presentation, quasi-coherence nor directedness is needed for
this purely categorical assembly. Empty chart families and empty overlaps are
covered by the same universal-property construction. -/
theorem exists_overlap_pair_transitions_comparison
    {X Y : Scheme.{u}} (U : X.OpenCover.{u})
    (N : (a : U.I₀) → (U.X a).Modules) (p : Y ⟶ X)
    (D : modulesPseudofunctor.DescentData (U.pullback₁ p).f)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom p a)).obj (N a) ≅ D.obj a)
    (φ : ∀ a b, (Scheme.Modules.pullback (pullback.fst (U.f a) (U.f b))).obj (N a) ⟶
      (Scheme.Modules.pullback (pullback.snd (U.f a) (U.f b))).obj (N b))
    (h : ∀ a b, overlapPairSquare U N p D e a b (φ a b)) :
    ∃ T : modulesPseudofunctor.OverlapTransitions U.f,
      (∀ a, T.obj a = N a) ∧
      Nonempty ((T.pull (p := p) (α := fun a ↦ a)
        (fun a ↦ U.pullbackHom_map p a)).Comparison D) := by
  exact Pseudofunctor.assemblePairs modulesPseudofunctor U.f (U.pullback₁ p).f p
    (fun a ↦ U.pullbackHom p a) (fun a ↦ U.pullbackHom_map p a) N D e φ h

end AlgebraicGeometry
