/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.EffacingSequenceComparison
import WeilConjectures.CategoryTheory.EffacingSequencePushout

/-!
# Successor transformations by effacement

Source: Stacks Project, Homology, Lemma 010T and the parent node's comparison arguments.
(blueprint: lem-weil-pbc-effaceable-delta-functor-successor).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory
namespace CategoryTheory

open Category Limits

private theorem effacing_delta_epi
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] (F : CohomologicalDeltaFunctor A B) (n : ℕ)
    (S : ShortComplex A) (hS : S.ShortExact) (hs : (F.F (n + 1)).map S.f = 0) :
    Epi (F.delta S hS n) := by
  obtain ⟨h, he⟩ := F.exact_left S hS n
  exact he.epi_f hs

private theorem effacing_candidate
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] (F G : CohomologicalDeltaFunctor A B) (n : ℕ)
    (t : F.F n ⟶ G.F n) (S : ShortComplex A) (hS : S.ShortExact)
    (hs : (F.F (n + 1)).map S.f = 0) :
    ∃ c : (F.F (n + 1)).obj S.X₁ ⟶ (G.F (n + 1)).obj S.X₁,
      F.delta S hS n ≫ c = t.app S.X₃ ≫ G.delta S hS n := by
  have : Epi (F.delta S hS n) := effacing_delta_epi F n S hS hs
  obtain ⟨h, he⟩ := F.exact_right S hS n
  obtain ⟨hg, heg⟩ := G.exact_right S hS n
  have hz : (F.F n).map S.g ≫ (t.app S.X₃ ≫ G.delta S hS n) = 0 := by
    rw [← Category.assoc, t.naturality, Category.assoc, hg, comp_zero]
  exact ⟨(CokernelCofork.IsColimit.desc' he.gIsCokernel _ hz).1,
    (CokernelCofork.IsColimit.desc' he.gIsCokernel _ hz).2⟩

private theorem candidate_comparison
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] (F G : CohomologicalDeltaFunctor A B) (n : ℕ)
    (t : F.F n ⟶ G.F n) (S T : ShortComplex A) (hS : S.ShortExact)
    (hT : T.ShortExact) (hs : (F.F (n + 1)).map S.f = 0) (p : S ⟶ T)
    (c : (F.F (n + 1)).obj S.X₁ ⟶ (G.F (n + 1)).obj S.X₁)
    (d : (F.F (n + 1)).obj T.X₁ ⟶ (G.F (n + 1)).obj T.X₁)
    (hc : F.delta S hS n ≫ c = t.app S.X₃ ≫ G.delta S hS n)
    (hd : F.delta T hT n ≫ d = t.app T.X₃ ≫ G.delta T hT n) :
    (F.F (n + 1)).map p.τ₁ ≫ d = c ≫ (G.F (n + 1)).map p.τ₁ := by
  have : Epi (F.delta S hS n) := effacing_delta_epi F n S hS hs
  apply (cancel_epi (F.delta S hS n)).mp
  calc
    F.delta S hS n ≫ ((F.F (n + 1)).map p.τ₁ ≫ d) =
        (F.F n).map p.τ₃ ≫ (F.delta T hT n ≫ d) := by
          rw [← Category.assoc, F.naturality S T hS hT p n, Category.assoc]
    _ = (F.F n).map p.τ₃ ≫ (t.app T.X₃ ≫ G.delta T hT n) := by rw [hd]
    _ = t.app S.X₃ ≫ (G.delta S hS n ≫ (G.F (n + 1)).map p.τ₁) := by
          rw [← Category.assoc, t.naturality, Category.assoc, G.naturality S T hS hT p n]
    _ = F.delta S hS n ≫ (c ≫ (G.F (n + 1)).map p.τ₁) := by
          simp only [← Category.assoc, hc]

/-- The induction step of Grothendieck's effacement construction.

Source: Stacks Project, Homology, Lemma 010T, construction of the successor degree.
Choose an effacing embedding of each object and take its cokernel short exact sequence.
Exactness makes the connecting map a cokernel of the preceding map, so the given
transformation induces a unique successor component. Compare two such embeddings using
their direct sum: the projections induce morphisms of short exact sequences, and
cancellation of the epimorphic connecting map proves independence and naturality.
Finally push out an arbitrary short exact sequence along an effacing embedding; its
map to an effacing sequence, together with naturality of connecting maps, proves the
required compatibility for every short exact sequence.
(blueprint: lem-weil-pbc-effaceable-delta-functor-successor) -/
theorem effaceable_deltaFunctor_successor
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ (n : ℕ), 0 < n → ∀ (X : A),
      ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F.F n).map u = 0)
    (G : CohomologicalDeltaFunctor A B) (n : ℕ) (t : F.F n ⟶ G.F n) :
    ∃ t' : F.F (n + 1) ⟶ G.F (n + 1),
      ∀ (S : ShortComplex A) (hS : S.ShortExact),
        F.delta S hS n ≫ t'.app S.X₁ = t.app S.X₃ ≫ G.delta S hS n := by
  classical
  let Y (X : A) := (hF (n + 1) (Nat.zero_lt_succ n) X).choose
  let u (X : A) : X ⟶ Y X := (hF (n + 1) (Nat.zero_lt_succ n) X).choose_spec.choose
  have hu (X : A) : Mono (u X) ∧ (F.F (n + 1)).map (u X) = 0 :=
    (hF (n + 1) (Nat.zero_lt_succ n) X).choose_spec.choose_spec
  let S (X : A) := ShortComplex.cokernelSequence (u X)
  have hS (X : A) : (S X).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (u X))
      (hu X).1 inferInstance
  let c (X : A) : (F.F (n + 1)).obj X ⟶ (G.F (n + 1)).obj X :=
    (effacing_candidate F G n t (S X) (hS X) (hu X).2).choose
  have hc (X : A) : F.delta (S X) (hS X) n ≫ c X =
      t.app (S X).X₃ ≫ G.delta (S X) (hS X) n :=
    (effacing_candidate F G n t (S X) (hS X) (hu X).2).choose_spec
  have hcan (T : ShortComplex A) (hT : T.ShortExact)
      (ht : (F.F (n + 1)).map T.f = 0) :
      F.delta T hT n ≫ c T.X₁ = t.app T.X₃ ≫ G.delta T hT n := by
    obtain ⟨Z, w, hw, hz, p, q, hp, hq⟩ :=
      effacingSequence_comparison F n T (S T.X₁) hT (hS T.X₁) ht (hu T.X₁).2 (𝟙 T.X₁)
    have hR : (ShortComplex.cokernelSequence w).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact w) hw inferInstance
    obtain ⟨d, hd⟩ := effacing_candidate F G n t _ hR hz
    dsimp only [ShortComplex.cokernelSequence] at d
    obtain ⟨e, he⟩ := effacing_candidate F G n t T hT ht
    have h1 := candidate_comparison F G n t _ T hR hT hz p d e hd he
    have h2 := candidate_comparison F G n t _ (S T.X₁) hR (hS T.X₁) hz q d (c T.X₁)
      hd (hc T.X₁)
    dsimp only [S, ShortComplex.cokernelSequence] at h1 h2
    simp only [hp, hq, Functor.map_id, id_comp, comp_id] at h1 h2
    rw [h2, ← h1]
    exact he
  refine ⟨{ app := c, naturality := ?_ }, ?_⟩
  · intro X X' a
    obtain ⟨Z, w, hw, hz, p, q, hp, hq⟩ :=
      effacingSequence_comparison F n (S X) (S X') (hS X) (hS X')
        (hu X).2 (hu X').2 a
    have hR : (ShortComplex.cokernelSequence w).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact w) hw inferInstance
    obtain ⟨d, hd⟩ := effacing_candidate F G n t _ hR hz
    dsimp only [ShortComplex.cokernelSequence] at d
    have h1 := candidate_comparison F G n t _ (S X) hR (hS X) hz p d (c X) hd (hc X)
    have h2 := candidate_comparison F G n t _ (S X') hR (hS X') hz q d (c X') hd (hc X')
    dsimp only [S, ShortComplex.cokernelSequence] at h1 h2
    simp [hp, S, ShortComplex.cokernelSequence] at h1
    simpa only [hq, ← h1] using h2
  · intro T hT
    obtain ⟨Z, w, hw, hz, p, hp⟩ :=
      effacingSequence_pushout F n (fun X ↦ hF (n + 1) (Nat.zero_lt_succ n) X) T hT
    have hR : (ShortComplex.cokernelSequence w).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact w) hw inferInstance
    have hn : (F.F n).map p.τ₃ ≫ t.app (ShortComplex.cokernelSequence w).X₃ =
        t.app T.X₃ ≫ (G.F n).map p.τ₃ := t.naturality p.τ₃
    have hf := F.naturality T _ hT hR p n
    have hg := G.naturality T _ hT hR p n
    simp only [hp, Functor.map_id, comp_id] at hf hg
    change F.delta T hT n ≫ c T.X₁ = t.app T.X₃ ≫ G.delta T hT n
    rw [hf, Category.assoc, hcan _ hR hz, ← Category.assoc, hn,
      Category.assoc, ← hg]

end CategoryTheory
