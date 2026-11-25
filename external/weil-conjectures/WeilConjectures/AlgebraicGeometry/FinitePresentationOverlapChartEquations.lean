/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapTripleEventually
import Mathlib.Data.Finset.Order

/-! # Eventual equations on diagonal and threefold overlap charts

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-overlap-eventual-chart-equations). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def overlapChosenPair {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) : ChosenPullback f g where
  pullback := pullback f g
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := pullbackIsPullback _ _

private noncomputable def overlapChosenTriple {X₁ X₂ X₃ S : Scheme.{u}}
    {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) : ChosenPullback₃ h₁₂ h₂₃ h₁₃ := by
  let pb := overlapChosenPair h₁₂.p₂ h₂₃.p₁
  have w : (pb.p₁ ≫ h₁₂.p₁) ≫ f₁ = (pb.p₂ ≫ h₂₃.p₂) ≫ f₃ := by
    rw [Category.assoc, h₁₂.condition, ← Category.assoc, pb.condition,
      Category.assoc, h₂₃.condition, ← Category.assoc]
  refine { chosenPullback := pb, l := ?_ }
  refine
    { f := h₁₃.isPullback.lift (pb.p₁ ≫ h₁₂.p₁) (pb.p₂ ≫ h₂₃.p₂) w
      f_p₁ := ?_
      f_p₂ := ?_
      f_p := ?_ }
  · exact h₁₃.isPullback.lift_fst _ _ w
  · exact h₁₃.isPullback.lift_snd _ _ w
  · rw [← h₁₃.hp₁, ← Category.assoc, h₁₃.isPullback.lift_fst,
      Category.assoc, h₁₂.hp₁]

-- Keeping tests abstract avoids expanding concrete refinement maps during elaboration.
private theorem overlapChosenEquations {ι : Type u} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} (g : ∀ a, X a ⟶ S)
    (T : modulesPseudofunctor.OverlapTransitions g)
    (hself : ∀ a, T.hom (g a) (𝟙 _) (𝟙 _)
      (Category.id_comp _) (Category.id_comp _) = 𝟙 _)
    (hcomp : ∀ sq : ∀ a b, ChosenPullback (g a) (g b),
      ∀ sq₃ : ∀ a b d, ChosenPullback₃ (sq a b) (sq b d) (sq a d),
      ∀ a b d,
        T.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
          (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
        T.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
          (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
        T.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
          (sq₃ a b d).w₁ (sq₃ a b d).w₃) :
    ∃ sq : ∀ a b, ChosenPullback (g a) (g b),
    ∃ sq₃ : ∀ a b d, ChosenPullback₃ (sq a b) (sq b d) (sq a d),
      (∀ a, T.hom (g a) (𝟙 _) (𝟙 _)
        (Category.id_comp _) (Category.id_comp _) = 𝟙 _) ∧
      (∀ a b d,
        T.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
          (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
        T.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
          (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
        T.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
          (sq₃ a b d).w₁ (sq₃ a b d).w₃) := by
  let sq : ∀ a b, ChosenPullback (g a) (g b) :=
    fun a b ↦ overlapChosenPair (g a) (g b)
  let sq₃ : ∀ a b d, ChosenPullback₃ (sq a b) (sq b d) (sq a d) :=
    fun a b d ↦ overlapChosenTriple (sq a b) (sq b d) (sq a d)
  exact ⟨sq, sq₃, hself, hcomp sq sq₃⟩

set_option backward.isDefEq.respectTransparency true in
/-- The diagonal and triple equations for the prescribed transitions hold on
finite-stage universal test charts. No comparison with a global module is asserted.
Source: Stacks Project, Tag 01ZR, first proof (Zariski gluing), and Tag 05N7 (3).
(blueprint: lem-pc-fp-overlap-eventual-chart-equations).

Proof: At stage k form the diagonal defect on each cover chart and the
composition defect on each chosen threefold overlap. The latter is the difference
of T12 followed by T23 and T13, so both maps have the same source and target.
All these test schemes are quasi-compact: cover charts are affine opens in a
quasi-separated scheme, and the threefold overlaps are intersections of finitely
many such opens. Their maps to Spec(R_k) are quasi-compact. The source and target
modules are restrictions of T's components. The given component isomorphisms
identify them with pullbacks of the prescribed finitely presented quasi-coherent
N_a; pullback preserves these properties. In particular the sources have finite
type. Pullback commutes with subtraction and composition. Naturality of T and
coherence of its limit pullback therefore make the limit pullbacks of all defects
zero. Apply finitePresentation_zero_map_descent to each defect, with its test
scheme over Spec(R_k) as the initial model and initial stage k. The identity
base change is identified with the test scheme by the canonical pullback
isomorphism; the limit base change is identified with the corresponding limit
test scheme by the pullback universal properties. Each defect then vanishes at a
stage above k. There are finitely many cover members and triples, so directedness
gives a common upper bound l. Zero maps stay zero under further pullback, and the
pseudofunctor composition comparisons identify the resulting maps with the defects
of the prescribed T' at l. Use the base-changed pairwise and threefold pullbacks
as sq and sq3; their universal properties determine their objects up to canonical
isomorphism. The refinement maps remain the displayed pullback lifts, not new
choices of transitions. For an empty cover take l=k and the equations are vacuous.
The cited zero-map descent theorem already handles directed preorders. -/
theorem exists_finitePresentation_overlap_eventual_chart_equations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        (T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Coherent →
        ∃ (l : I) (hkl : k ≤ l),
          let q := overlapStageMap R f hij (hjk.trans hkl)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkl)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkl
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkl)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkl) a)
          ∃ sq : ∀ a b, ChosenPullback (V.f a) (V.f b),
          ∃ sq₃ : ∀ a b d, ChosenPullback₃ (sq a b) (sq b d) (sq a d),
            (∀ a, T'.hom (V.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) = 𝟙 _) ∧
            (∀ a b d,
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
                (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
                (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
                (sq₃ a b d).w₁ (sq₃ a b d).w₃)  := by
  classical
  intro k hjk
  dsimp only
  intro T hT hco
  let : Fintype U.I₀ := Fintype.ofFinite U.I₀
  have diagonal (a : U.I₀) := finitePresentation_overlap_diagonal_eventually
    R c hc i f j hij U N a hN hNq k hjk T hT hco
  have triple (abd : U.I₀ × U.I₀ × U.I₀) := finitePresentation_overlap_triple_eventually
    R c hc i f j hij U N abd.1 abd.2.1 abd.2.2 hN hNq k hjk T hT hco
  let ld : U.I₀ → I := fun a ↦ (diagonal a).choose
  have hd (a : U.I₀) := (diagonal a).choose_spec.choose_spec
  let lt : U.I₀ × U.I₀ × U.I₀ → I := fun abd ↦ (triple abd).choose
  have ht (abd : U.I₀ × U.I₀ × U.I₀) := (triple abd).choose_spec.choose_spec
  let : Nonempty I := ⟨k⟩
  obtain ⟨l, hl⟩ := (insert k
    ((Finset.univ.image ld) ∪ (Finset.univ.image lt))).exists_le
  have hkl : k ≤ l := hl k (Finset.mem_insert_self _ _)
  have hdle (a : U.I₀) : ld a ≤ l := hl (ld a) (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)))
  have htle (abd : U.I₀ × U.I₀ × U.I₀) : lt abd ≤ l :=
    hl (lt abd) (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨abd, Finset.mem_univ _, rfl⟩)))
  refine ⟨l, hkl, ?_⟩
  apply overlapChosenEquations
  · intro a
    exact hd a l hkl (hdle a)
  · intro sq sq₃ a b d
    have hh := ht (a, b, d) l hkl (htle (a, b, d))
    dsimp only at hh
    exact hh sq sq₃

end AlgebraicGeometry
