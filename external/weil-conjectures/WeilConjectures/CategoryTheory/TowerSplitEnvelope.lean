/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Functorial split envelope of an inverse system

Source: literature/stacks-project/derived.tex, the explicit replacement step
for Lemma Tag 070M (blueprint: lem-weil-tower-split-envelope).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def envelopeObj
    {C : Type u} [Category.{v} C] [Abelian C] (T : ℕᵒᵖ ⥤ C) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence
    (X := fun n ↦ ∏ᶜ fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) (fun n ↦
    Pi.lift (fun k : Fin (n + 1) ↦
      Pi.π (fun k : Fin (n + 1 + 1) ↦ T.obj (Opposite.op k.val)) k.castSucc))

private noncomputable def envelopeMap
    {C : Type u} [Category.{v} C] [Abelian C] {T T' : ℕᵒᵖ ⥤ C} (φ : T ⟶ T') :
    envelopeObj T ⟶ envelopeObj T' :=
  NatTrans.ofOpSequence
    (fun n ↦ Limits.Pi.map (fun k : Fin (n + 1) ↦ φ.app (Opposite.op k.val))) (by
      intro n
      apply Pi.hom_ext
      intro k
      simp [envelopeObj])

private noncomputable def envelope
    {C : Type u} [Category.{v} C] [Abelian C] : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ C) where
  obj := envelopeObj
  map := envelopeMap
  map_id T := by
    ext n
    dsimp [envelopeMap, NatTrans.ofOpSequence]
    simp [envelopeObj]
    rfl
  map_comp φ ψ := by
    ext n
    dsimp [envelopeMap, NatTrans.ofOpSequence]
    simp [Limits.Pi.map_comp_map]

private noncomputable def envelopeEmbedding
    {C : Type u} [Category.{v} C] [Abelian C] (T : ℕᵒᵖ ⥤ C) : T ⟶ envelopeObj T :=
  NatTrans.ofOpSequence
    (fun n ↦ Pi.lift (fun k : Fin (n + 1) ↦
      T.map (homOfLE (Nat.le_of_lt_succ k.isLt)).op)) (by
      intro n
      apply Pi.hom_ext
      intro k
      simp only [envelopeObj, Functor.ofOpSequence_map_homOfLE_succ,
        Category.assoc, Pi.lift_comp_π]
      rw [← T.map_comp]
      rfl)

private noncomputable def envelopeι
    {C : Type u} [Category.{v} C] [Abelian C] : 𝟭 (ℕᵒᵖ ⥤ C) ⟶ envelope (C := C) where
  app := envelopeEmbedding
  naturality := by
    intro T T' φ
    ext n
    apply Pi.hom_ext
    intro k
    simp only [Functor.id_map, envelope, envelopeMap, envelopeEmbedding,
      NatTrans.ofOpSequence_app, NatTrans.comp_app, Category.assoc, Pi.lift_comp_π,
      Limits.Pi.map_π, Pi.lift_comp_π_assoc]
    exact (φ.naturality _).symm

private theorem envelope_split
    {C : Type u} [Category.{v} C] [Abelian C] (T : ℕᵒᵖ ⥤ C) (n : ℕ) :
    IsSplitEpi ((envelopeObj T).map (homOfLE (Nat.le_succ n)).op) := by
  classical
  rw [envelopeObj, Functor.ofOpSequence_map_homOfLE_succ]
  refine IsSplitEpi.mk' ⟨Pi.lift (fun k ↦ Fin.lastCases 0
    (fun i ↦ Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) i) k), ?_⟩
  apply Pi.hom_ext
  intro k
  simp

private theorem embedding_split
    {C : Type u} [Category.{v} C] [Abelian C] (T : ℕᵒᵖ ⥤ C) (n : ℕ) :
    IsSplitMono ((envelopeEmbedding T).app (Opposite.op n)) := by
  refine IsSplitMono.mk' ⟨
    Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) (Fin.last n), ?_⟩
  simp [envelopeEmbedding]

private theorem split_cokernel_projection
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    IsSplitEpi (cokernel.π f) := by
  let p := 𝟙 Y - retraction f ≫ f
  have hp : f ≫ p = 0 := by simp [p, Preadditive.comp_sub, ← Category.assoc]
  refine IsSplitEpi.mk' ⟨cokernel.desc f p hp, ?_⟩
  apply (cancel_epi (cokernel.π f)).1
  simp [p, Preadditive.sub_comp]

private theorem split_cokernel_app
    {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category D]
    {F G : D ⥤ C} (j : F ⟶ G) (d : D) [IsSplitMono (j.app d)] :
    IsSplitEpi ((cokernel.π j).app d) := by
  let ev := (evaluation D C).obj d
  have : IsSplitMono (ev.map j) := by simpa [ev] using inferInstanceAs
    (IsSplitMono (j.app d))
  have : IsSplitEpi (cokernel.π (ev.map j)) := split_cokernel_projection _
  have : IsSplitEpi
      (cokernel.π (ev.map j) ≫ (PreservesCokernel.iso ev j).inv) := inferInstance
  have h : IsSplitEpi (ev.map (cokernel.π j)) := by
    simpa only [← PreservesCokernel.π_iso_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using this
  simpa [ev] using h

private theorem split_cokernel_transition
    {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category D]
    {F G : D ⥤ C} (j : F ⟶ G) {a b : D} (f : a ⟶ b)
    [IsSplitMono (j.app b)] [IsSplitEpi (G.map f)] :
    IsSplitEpi ((cokernel j).map f) := by
  let q := cokernel.π j
  have : IsSplitEpi (q.app b) := split_cokernel_app j b
  refine IsSplitEpi.mk' ⟨section_ (q.app b) ≫ section_ (G.map f) ≫ q.app a, ?_⟩
  rw [Category.assoc, Category.assoc, ← q.naturality f]
  simp only [← Category.assoc, IsSplitEpi.id, Category.id_comp]

/-- Functorial finite-product split envelope of towers with its natural embedding
and split cokernel. The index `n` represents the positive integer `n + 1`.
The isomorphisms `e` identify each envelope term with the specified finite product;
the three component equations specify its transition projections, its action on
morphisms, and the embedding by composites of the original transition maps.

Source: literature/stacks-project/derived.tex, explicit replacement step for
Lemma Tag 070M (lemma-difficulty-K-injectives).

Proof:
1. By `def-sp-abelian`, finite products are biproducts. Use their projections and
   injections and the composite transition maps of `def-weil-inverse-system`.
2. Define the action on morphisms componentwise. Comparing projections proves
   compatibility with transitions, preservation of identities and composition,
   and additivity by bilinearity (`def-weil-preadditive-category`).
3. The envelope transitions forget the last factor; inclusion with zero last
   component is a section (`def-weil-additive-category`).
4. The identities f(m+1,k) = f(m+1,m) followed by f(m,k) show that j is a tower
   morphism. Naturality of the original tower morphisms gives naturality of j.
   The last projection retracts each component of j, proving it monic.
   By `lem-weil-tower-category-levelwise-abelian`, cokernels are computed levelwise.
5. The automorphism subtracting f(m,k) times the last component from each earlier
   component carries j to the last summand injection. Its inverse adds these
   terms. Thus projection to the earlier factors after this automorphism is a
   cokernel, identifying C(m) with the product of the factors before m (zero at 1).
6. The induced cokernel transition is the map with components pr(k)-f(m,k)pr(m):
   this follows by expanding its composite with the preceding cokernel projection
   and cancelling using f(m+1,k)=f(m,k)f(m+1,m). Inclusion with last component
   zero is its section. Uniqueness of cokernels transports these sections to the
   chosen cokernel tower, proving it split.
(blueprint: lem-weil-tower-split-envelope) -/
theorem tower_split_envelope
    {C : Type u} [Category.{v} C] [Abelian C] :
    ∃ (E : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ C)) (j : 𝟭 (ℕᵒᵖ ⥤ C) ⟶ E)
      (e : ∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ),
        (E.obj T).obj (Opposite.op n) ≅
          ∏ᶜ fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)),
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ) (k : Fin (n + 1)),
        (E.obj T).map (homOfLE (Nat.le_succ n)).op ≫ (e T n).hom ≫
          Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) k =
        (e T (n + 1)).hom ≫
          Pi.π (fun k : Fin (n + 1 + 1) ↦ T.obj (Opposite.op k.val)) k.castSucc) ∧
      (∀ (T T' : ℕᵒᵖ ⥤ C) (φ : T ⟶ T') (n : ℕ) (k : Fin (n + 1)),
        (E.map φ).app (Opposite.op n) ≫ (e T' n).hom ≫
          Pi.π (fun k : Fin (n + 1) ↦ T'.obj (Opposite.op k.val)) k =
        (e T n).hom ≫ Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) k ≫
          φ.app (Opposite.op k.val)) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ) (k : Fin (n + 1)),
        (j.app T).app (Opposite.op n) ≫ (e T n).hom ≫
          Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) k =
        T.map (homOfLE (Nat.le_of_lt_succ k.isLt)).op) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ),
        IsSplitEpi ((E.obj T).map (homOfLE (Nat.le_succ n)).op)) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ), Mono ((j.app T).app (Opposite.op n))) ∧
      (∀ (T T' : ℕᵒᵖ ⥤ C) (φ ψ : T ⟶ T'), E.map (φ + ψ) = E.map φ + E.map ψ) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ),
        IsSplitEpi ((cokernel (j.app T)).map (homOfLE (Nat.le_succ n)).op)) := by
  refine ⟨envelope, envelopeι, (fun T n ↦ Iso.refl _), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T n k
    simp [envelope, envelopeObj]
  · intro T T' φ n k
    simp [envelope, envelopeMap, envelopeObj]
  · intro T n k
    simp [envelopeι, envelopeEmbedding]
  · exact envelope_split
  · intro T n
    have := embedding_split T n
    exact inferInstanceAs (Mono ((envelopeEmbedding T).app (Opposite.op n)))
  · intro T T' φ ψ
    ext n
    apply Pi.hom_ext
    intro k
    simp [envelope, envelopeMap, Preadditive.add_comp, Preadditive.comp_add]
  · intro T n
    have := embedding_split T n
    have := envelope_split T n
    exact split_cokernel_transition (envelopeEmbedding T) _

end CategoryTheory
