/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fin.VecNotation

/-!
# Compatible local cones on finite families of hypercover simplices

Source: Stacks Project, Hypercoverings, Tag 01GE, and the finite-support argument in
lem-weil-pbc-ringed-hypercover-injective-augmentation.
(auxiliary; not a blueprint node).

The cone functions retain the original labels before restriction. This permits the
alternating cone identity even when distinct labels become equal on a covering member.
-/

@[expose] public section

universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.RingedHypercover
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Local lifting of every compatible lower-simplex matching family over the augmentation.
This is the explicit hypercover hypothesis used in the injective augmentation theorem. -/
def HasLocalLifts (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) : Prop :=
  ∀ (n : ℕ) (T : C) (w : T ⟶ W)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.obj (op Δ))),
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ e.app (op Δ) = w) →
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)) →
      ∃ K : Sieve T, K ∈ J T ∧
        ∀ (V : C) (f : V ⟶ T), K f →
          ∃ t : V ⟶ U _⦋n⦌,
            t ≫ e.app (op (SimplexCategory.mk n)) = f ≫ w ∧
            ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
              t ≫ U.map θ.op = f ≫ p Δ h θ

/-- Two vertices with the same augmentation are locally the two faces of an edge.
Source: Stacks Project, Tag 01GE, degree-one matching surjectivity.
(auxiliary; not a blueprint node). -/
lemma local_edge (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) (hcover : HasLocalLifts J W U e)
    (T : C) (a b : T ⟶ U _⦋0⦌) (hab : a ≫ e.app (op ⦋0⦌) = b ≫ e.app (op ⦋0⦌)) :
    ∃ K : Sieve T, K ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), K f →
      ∃ t : V ⟶ U _⦋1⦌, t ≫ U.δ 0 = f ≫ a ∧ t ≫ U.δ 1 = f ≫ b := by
  classical
  let p : ∀ Δ : SimplexCategory, Δ.len < 1 → (Δ ⟶ ⦋1⦌) → (T ⟶ U.obj (op Δ)) := by
    rintro ⟨n⟩ hn θ
    have hn' : n = 0 := by exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    subst n
    exact if θ.toOrderHom 0 = 1 then a else b
  have hp (Δ : SimplexCategory) (h : Δ.len < 1) (θ : Δ ⟶ ⦋1⦌) :
      p Δ h θ ≫ e.app (op Δ) = a ≫ e.app (op ⦋0⦌) := by
    obtain ⟨n⟩ := Δ
    have hn : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
    subst n
    dsimp [p]
    split_ifs <;> first | rfl | exact hab.symm
  have hcompat (Δ Δ' : SimplexCategory) (h : Δ.len < 1) (h' : Δ'.len < 1)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ ⦋1⦌) : p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ) := by
    obtain ⟨n⟩ := Δ
    obtain ⟨m⟩ := Δ'
    have hn : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
    have hm : m = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h')
    subst n; subst m
    rw [SimplexCategory.hom_zero_zero α]
    simp
  obtain ⟨K, hK, ht⟩ := hcover 1 T (a ≫ e.app (op ⦋0⦌)) p hp hcompat
  refine ⟨K, hK, fun V f hf ↦ ?_⟩
  obtain ⟨t, _, ht⟩ := ht V f hf
  refine ⟨t, ?_, ?_⟩
  · simpa [p, SimplicialObject.δ, SimplexCategory.δ] using ht ⦋0⦌ (by decide) (SimplexCategory.δ 0)
  · simpa [p, SimplicialObject.δ, SimplexCategory.δ] using ht ⦋0⦌ (by decide) (SimplexCategory.δ 1)



/-- Finitely many local lifting conditions can be imposed on one covering sieve. -/
private lemma finite_local_conditions {A : Type*} (T : C) (s : Finset A)
    (P : A → ∀ (V : C), (V ⟶ T) → Prop)
    (h : ∀ a ∈ s, ∃ K : Sieve T, K ∈ J T ∧
      ∀ (V : C) (f : V ⟶ T), K f → P a V f) :
    ∃ K : Sieve T, K ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), K f → ∀ a ∈ s, P a V f := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, J.top_mem T, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨K, hK, hKa⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨L, hL, hLs⟩ := ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb))
    refine ⟨K ⊓ L, J.intersection_covering hK hL, fun V f hf b hb ↦ ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hKa V f hf.1
    · exact hLs V f hf.2 b hb

private lemma finite_local_lifts {A : Type*} (T : C) (s : Finset A) (hs : s.Nonempty)
    (B : C → Type*) (P : A → ∀ (V : C), (V ⟶ T) → B V → Prop)
    (h : ∀ a ∈ s, ∃ K : Sieve T, K ∈ J T ∧
      ∀ (V : C) (f : V ⟶ T), K f → ∃ b, P a V f b) :
    ∃ K : Sieve T, K ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), K f →
      ∃ b : A → B V, ∀ a ∈ s, P a V f (b a) := by
  classical
  obtain ⟨K, hK, hP⟩ := finite_local_conditions J T s (fun a V f ↦ ∃ b, P a V f b) h
  refine ⟨K, hK, fun V f hf ↦ ?_⟩
  let b : A → B V := fun a ↦ if ha : a ∈ s then (hP V f hf a ha).choose
    else (hP V f hf hs.choose hs.choose_spec).choose
  refine ⟨b, fun a ha ↦ ?_⟩
  simpa only [b, dite_eq_left ha] using (hP V f hf a ha).choose_spec

private lemma face_family_independent (U : SimplicialObject C) (n m : ℕ) (T : C)
    (b : Fin (n + 3) → (T ⟶ U _⦋n + 1⦌))
    (hb : ∀ (i j : Fin (n + 3)) (h : i < j),
      b j ≫ U.δ (i.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ j.isLt))) =
        b i ≫ U.δ (j.pred (Fin.ne_zero_of_lt h)))
    (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) (i j : Fin (n + 3))
    (hi : ∀ k, θ.toOrderHom k ≠ i) (hj : ∀ k, θ.toOrderHom k ≠ j) :
    b i ≫ U.map (SimplexCategory.factor_δ θ i).op =
      b j ≫ U.map (SimplexCategory.factor_δ θ j).op := by
  classical
  wlog hij : i < j generalizing i j
  · rcases lt_trichotomy i j with h | rfl | h
    · exact this i j hi hj h
    · rfl
    · exact (this j i hj hi h).symm
  let i' : Fin (n + 2) := i.castLT (Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt))
  let j' : Fin (n + 2) := j.pred (Fin.ne_zero_of_lt hij)
  have hi' : i'.castSucc = i := by apply Fin.ext; rfl
  have hδi : (SimplexCategory.δ j).toOrderHom i' = i := by
    change j.succAbove i' = i
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa only [hi'] using hij)]
    exact hi'
  have hjmiss : ∀ k, (SimplexCategory.factor_δ θ j).toOrderHom k ≠ i' := by
    intro k hk
    have he := congrArg (fun f : ⦋m⦌ ⟶ ⦋n + 2⦌ ↦ f.toOrderHom k)
      (SimplexCategory.factor_δ_spec θ j hj)
    change (SimplexCategory.δ j).toOrderHom
      ((SimplexCategory.factor_δ θ j).toOrderHom k) = θ.toOrderHom k at he
    rw [hk, hδi] at he
    exact hi k he.symm
  let η := SimplexCategory.factor_δ (SimplexCategory.factor_δ θ j) i'
  have hη : η ≫ SimplexCategory.δ i' = SimplexCategory.factor_δ θ j :=
    SimplexCategory.factor_δ_spec _ i' hjmiss
  have hδδ : SimplexCategory.δ i' ≫ SimplexCategory.δ j =
      SimplexCategory.δ j' ≫ SimplexCategory.δ i := by
    have he := SimplexCategory.δ_comp_δ' (n := n)
      (i := i') (j := j) (by simpa only [hi'] using hij)
    simpa only [hi'] using he
  have hηi : η ≫ SimplexCategory.δ j' = SimplexCategory.factor_δ θ i := by
    apply (cancel_mono (SimplexCategory.δ i)).mp
    calc
      (η ≫ SimplexCategory.δ j') ≫ SimplexCategory.δ i =
          η ≫ (SimplexCategory.δ i' ≫ SimplexCategory.δ j) := by rw [Category.assoc, hδδ]
      _ = θ := by rw [← Category.assoc, hη, SimplexCategory.factor_δ_spec θ j hj]
      _ = _ := (SimplexCategory.factor_δ_spec θ i hi).symm
  rw [← hηi, ← hη, op_comp, op_comp, U.map_comp, U.map_comp]
  simpa only [Category.assoc, SimplicialObject.δ, i', j'] using
    congrArg (fun f ↦ f ≫ U.map η.op) (hb i j hij).symm

private lemma exists_matching_family_of_faces (U : SimplicialObject C) (n : ℕ) (T : C)
    (b : Fin (n + 3) → (T ⟶ U _⦋n + 1⦌))
    (hb : ∀ (i j : Fin (n + 3)) (h : i < j),
      b j ≫ U.δ (i.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ j.isLt))) =
        b i ≫ U.δ (j.pred (Fin.ne_zero_of_lt h))) :
    ∃ p : ∀ Δ : SimplexCategory, Δ.len < n + 2 → (Δ ⟶ ⦋n + 2⦌) → (T ⟶ U.obj (op Δ)),
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n + 2) (h' : Δ'.len < n + 2)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ ⦋n + 2⦌),
        p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)) ∧
      ∀ i : Fin (n + 3), p ⦋n + 1⦌ (Nat.lt_succ_self _) (SimplexCategory.δ i) = b i := by
  classical
  have hex (m : ℕ) (h : m < n + 2) (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) :
      ∃ i : Fin (n + 3), ∀ k, θ.toOrderHom k ≠ i := by
    by_contra! hn
    have hs : Function.Surjective θ.toOrderHom := fun i ↦ hn i
    have he := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at he
    omega
  let p : ∀ Δ : SimplexCategory, Δ.len < n + 2 → (Δ ⟶ ⦋n + 2⦌) → (T ⟶ U.obj (op Δ)) :=
    fun Δ h θ ↦ b (hex Δ.len h θ).choose ≫
      U.map (SimplexCategory.factor_δ θ (hex Δ.len h θ).choose).op
  refine ⟨p, ?_, ?_⟩
  · intro Δ Δ' h h' α θ
    let i := (hex Δ.len h θ).choose
    let j := (hex Δ'.len h' (α ≫ θ)).choose
    have hi := (hex Δ.len h θ).choose_spec
    have hj := (hex Δ'.len h' (α ≫ θ)).choose_spec
    have hiα : ∀ k, (α ≫ θ).toOrderHom k ≠ i := fun k ↦ hi (α.toOrderHom k)
    have hfac : α ≫ SimplexCategory.factor_δ θ i =
        SimplexCategory.factor_δ (α ≫ θ) i := by
      apply (cancel_mono (SimplexCategory.δ i)).mp
      rw [Category.assoc, SimplexCategory.factor_δ_spec θ i hi,
        SimplexCategory.factor_δ_spec (α ≫ θ) i hiα]
    change (b i ≫ U.map (SimplexCategory.factor_δ θ i).op) ≫ U.map α.op =
      b j ≫ U.map (SimplexCategory.factor_δ (α ≫ θ) j).op
    rw [Category.assoc, ← U.map_comp, ← op_comp, hfac]
    exact face_family_independent U n Δ'.len T b hb (α ≫ θ) i j hiα hj
  · intro i
    let j := (hex (n + 1) (by omega) (SimplexCategory.δ i)).choose
    have hi : ∀ k, (SimplexCategory.δ i).toOrderHom k ≠ i := Fin.succAbove_ne i
    have hj := (hex (n + 1) (by omega) (SimplexCategory.δ i)).choose_spec
    have he := face_family_independent U n (n + 1) T b hb (SimplexCategory.δ i) j i hj hi
    have hfac : SimplexCategory.factor_δ (SimplexCategory.δ i) i = 𝟙 _ := by
      apply (cancel_mono (SimplexCategory.δ i)).mp
      rw [SimplexCategory.factor_δ_spec (SimplexCategory.δ i) i hi, Category.id_comp]
    change b j ≫ U.map (SimplexCategory.factor_δ (SimplexCategory.δ i) j).op = b i
    rw [he, hfac, op_id, U.map_id, Category.comp_id]

private lemma local_face_lift (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) (hcover : HasLocalLifts J W U e)
    (n : ℕ) (T : C) (w : T ⟶ W) (b : Fin (n + 3) → (T ⟶ U _⦋n + 1⦌))
    (hb : ∀ (i j : Fin (n + 3)) (h : i < j),
      b j ≫ U.δ (i.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ j.isLt))) =
        b i ≫ U.δ (j.pred (Fin.ne_zero_of_lt h)))
    (haug : ∀ i, b i ≫ e.app (op ⦋n + 1⦌) = w) :
    ∃ K : Sieve T, K ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), K f →
      ∃ t : V ⟶ U _⦋n + 2⦌, ∀ i : Fin (n + 3), t ≫ U.δ i = f ≫ b i := by
  classical
  obtain ⟨p, hp, hpi⟩ := exists_matching_family_of_faces U n T b hb
  have hpa (Δ : SimplexCategory) (h : Δ.len < n + 2) (θ : Δ ⟶ ⦋n + 2⦌) :
      p Δ h θ ≫ e.app (op Δ) = w := by
    have hex : ∃ i : Fin (n + 3), ∀ k, θ.toOrderHom k ≠ i := by
      by_contra! hn
      have he := Fintype.card_le_of_surjective θ.toOrderHom (fun i ↦ hn i)
      simp only [Fintype.card_fin] at he
      omega
    obtain ⟨i, hi⟩ := hex
    let α := SimplexCategory.factor_δ θ i
    have hα : α ≫ SimplexCategory.δ i = θ := SimplexCategory.factor_δ_spec θ i hi
    have hcomp := hp ⦋n + 1⦌ Δ (Nat.lt_succ_self _) h α (SimplexCategory.δ i)
    rw [hpi, hα] at hcomp
    rw [← hcomp, Category.assoc]
    have he : U.map α.op ≫ e.app (op Δ) = e.app (op ⦋n + 1⦌) :=
      (e.naturality α.op).trans (Category.comp_id _)
    rw [he, haug]
  obtain ⟨K, hK, ht⟩ := hcover (n + 2) T w p hpa hp
  refine ⟨K, hK, fun V f hf ↦ ?_⟩
  obtain ⟨t, _, ht⟩ := ht V f hf
  refine ⟨t, fun i ↦ ?_⟩
  have hh := ht ⦋n + 1⦌ (Nat.lt_succ_self _) (SimplexCategory.δ i)
  rw [hpi] at hh
  exact hh

private lemma finite_local_cones_zero (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) (hcover : HasLocalLifts J W U e)
    (T : C) (A : Finset (ULift.{v} (T ⟶ U _⦋1⦌))) (hA : A.Nonempty) :
    ∃ K : Sieve T, K ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), K f →
      ∃ (c : ULift.{v} (T ⟶ U _⦋1⦌) → (V ⟶ U _⦋2⦌))
        (b : ULift.{v} (T ⟶ U _⦋0⦌) → (V ⟶ U _⦋1⦌)),
        ∀ a ∈ A, c a ≫ U.δ 0 = f ≫ a.down ∧
          ∀ i : Fin 2, c a ≫ U.δ i.succ = b (ULift.up (a.down ≫ U.δ i)) := by
  classical
  let B := A.biUnion (fun a ↦ Finset.univ.image
    (fun i : Fin 2 ↦ (ULift.up (a.down ≫ U.δ i) : ULift.{v} (T ⟶ U _⦋0⦌))))
  have hB (a : ULift.{v} (T ⟶ U _⦋1⦌)) (ha : a ∈ A) (i : Fin 2) :
      ULift.up (a.down ≫ U.δ i) ∈ B := by
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hBne : B.Nonempty := ⟨_, hB hA.choose hA.choose_spec 0⟩
  let : Nonempty (ULift.{v} (T ⟶ U _⦋0⦌)) := ⟨hBne.choose⟩
  let aug : ULift.{v} (T ⟶ U _⦋0⦌) → ULift.{v} (T ⟶ W) :=
    fun a ↦ ULift.up (a.down ≫ e.app (op ⦋0⦌))
  let base := Function.invFun aug
  have hbase (a : ULift.{v} (T ⟶ U _⦋0⦌)) :
      (base (aug a)).down ≫ e.app (op ⦋0⦌) = a.down ≫ e.app (op ⦋0⦌) :=
    congrArg ULift.down (Function.invFun_eq (f := aug) ⟨a, rfl⟩)
  obtain ⟨K, hKmem, hK⟩ := finite_local_lifts J T B hBne (fun V ↦ V ⟶ U _⦋1⦌)
    (fun a V f b ↦ b ≫ U.δ 0 = f ≫ a.down ∧ b ≫ U.δ 1 = f ≫ (base (aug a)).down)
    (fun a _ ↦ local_edge J W U e hcover T a.down (base (aug a)).down (hbase a).symm)
  have hrefine (V : C) (f : V ⟶ T) (hf : K f) :
      ∃ Q : Sieve V, Q ∈ J V ∧ ∀ (Z : C) (g : Z ⟶ V), Q g →
        ∃ (c : ULift.{v} (T ⟶ U _⦋1⦌) → (Z ⟶ U _⦋2⦌))
          (b : ULift.{v} (T ⟶ U _⦋0⦌) → (Z ⟶ U _⦋1⦌)),
          ∀ a ∈ A, c a ≫ U.δ 0 = (g ≫ f) ≫ a.down ∧
            ∀ i : Fin 2, c a ≫ U.δ i.succ = b (ULift.up (a.down ≫ U.δ i)) := by
    obtain ⟨b, hb⟩ := hK V f hf
    let faces (a : ULift.{v} (T ⟶ U _⦋1⦌)) : Fin 3 → (V ⟶ U _⦋1⦌) :=
      ![f ≫ a.down, b (ULift.up (a.down ≫ U.δ 0)), b (ULift.up (a.down ≫ U.δ 1))]
    have hcompat (a : ULift.{v} (T ⟶ U _⦋1⦌)) (ha : a ∈ A)
        (i j : Fin 3) (hij : i < j) :
        faces a j ≫ U.δ (i.castLT (Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt))) =
          faces a i ≫ U.δ (j.pred (Fin.ne_zero_of_lt hij)) := by
      have h0 := hb (ULift.up (a.down ≫ U.δ 0)) (hB a ha 0)
      have h1 := hb (ULift.up (a.down ≫ U.δ 1)) (hB a ha 1)
      have haug : aug (ULift.up (a.down ≫ U.δ 0)) = aug (ULift.up (a.down ≫ U.δ 1)) := by
        apply ULift.ext
        change (a.down ≫ U.δ 0) ≫ e.app (op ⦋0⦌) =
          (a.down ≫ U.δ 1) ≫ e.app (op ⦋0⦌)
        have he0 := (e.naturality (SimplexCategory.δ (0 : Fin 2)).op).trans (Category.comp_id _)
        have he1 := (e.naturality (SimplexCategory.δ (1 : Fin 2)).op).trans (Category.comp_id _)
        simpa only [Category.assoc, SimplicialObject.δ] using
          (congrArg (fun t ↦ a.down ≫ t) he0).trans
          (congrArg (fun t ↦ a.down ≫ t) he1).symm
      rw [haug] at h0
      fin_cases i <;> fin_cases j <;> simp only [Fin.lt_def] at hij <;> norm_num at hij
      · simpa [faces, Category.assoc] using h0.1
      · simpa [faces, Category.assoc] using h1.1
      · simpa [faces, haug] using h1.2.trans h0.2.symm
    have haug (a : ULift.{v} (T ⟶ U _⦋1⦌)) (ha : a ∈ A) (i : Fin 3) :
        faces a i ≫ e.app (op ⦋1⦌) = f ≫ a.down ≫ e.app (op ⦋1⦌) := by
      have he : U.δ (0 : Fin 2) ≫ e.app (op ⦋0⦌) = e.app (op ⦋1⦌) :=
        (e.naturality (SimplexCategory.δ (0 : Fin 2)).op).trans (Category.comp_id _)
      have hva (j : Fin 2) : U.δ j ≫ e.app (op ⦋0⦌) = e.app (op ⦋1⦌) :=
        (e.naturality (SimplexCategory.δ j).op).trans (Category.comp_id _)
      fin_cases i
      · simp [faces]
      · change b _ ≫ e.app (op ⦋1⦌) = _
        rw [← he, ← Category.assoc, (hb _ (hB a ha 0)).1]
        simp only [Category.assoc, hva]
      · change b _ ≫ e.app (op ⦋1⦌) = _
        rw [← he, ← Category.assoc, (hb _ (hB a ha 1)).1]
        simp only [Category.assoc, hva]
    obtain ⟨Q, hQ, hc⟩ := finite_local_lifts J V A hA (fun Z ↦ Z ⟶ U _⦋2⦌)
      (fun a Z g c ↦ ∀ i : Fin 3, c ≫ U.δ i = g ≫ faces a i)
      (fun a ha ↦ local_face_lift J W U e hcover 0 V
        (f ≫ a.down ≫ e.app (op ⦋1⦌)) (faces a) (hcompat a ha) (haug a ha))
    refine ⟨Q, hQ, fun Z g hg ↦ ?_⟩
    obtain ⟨c, hc⟩ := hc Z g hg
    refine ⟨c, fun a ↦ g ≫ b a, fun a ha ↦ ?_⟩
    refine ⟨?_, fun i ↦ ?_⟩
    · simpa [faces, Category.assoc] using hc a ha 0
    · fin_cases i
      · simpa [faces] using hc a ha 1
      · simpa [faces] using hc a ha 2
  choose Q hQ hprop using hrefine
  refine ⟨Sieve.bind K (fun {V} {f} hf ↦ Q V f hf),
    J.bind_covering hKmem (fun V f hf ↦ hQ V f hf), fun Z h hh ↦ ?_⟩
  obtain ⟨V, g, f, hf, hg, rfl⟩ := hh
  exact hprop V f hf Z g hg

private lemma cone_faces_compatible (U : SimplicialObject C) (n : ℕ) (T V : C) (f : V ⟶ T)
    (a : T ⟶ U _⦋n + 2⦌)
    (c : ULift.{v} (T ⟶ U _⦋n + 1⦌) → (V ⟶ U _⦋n + 2⦌))
    (b : ULift.{v} (T ⟶ U _⦋n⦌) → (V ⟶ U _⦋n + 1⦌))
    (h0 : ∀ i : Fin (n + 3), c (ULift.up (a ≫ U.δ i)) ≫ U.δ 0 = f ≫ a ≫ U.δ i)
    (hs : ∀ (i : Fin (n + 3)) (j : Fin (n + 2)),
      c (ULift.up (a ≫ U.δ i)) ≫ U.δ j.succ = b (ULift.up ((a ≫ U.δ i) ≫ U.δ j))) :
    let faces : Fin (n + 4) → (V ⟶ U _⦋n + 2⦌) :=
      Fin.cases (f ≫ a) (fun i ↦ c (ULift.up (a ≫ U.δ i)))
    ∀ (i j : Fin (n + 4)) (h : i < j),
      faces j ≫ U.δ (i.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ j.isLt))) =
        faces i ≫ U.δ (j.pred (Fin.ne_zero_of_lt h)) := by
  intro faces i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (lt_irrefl _ hij).elim
    | succ j =>
      change c (ULift.up (a ≫ U.δ j)) ≫ U.δ 0 = (f ≫ a) ≫ U.δ j
      simpa only [Category.assoc] using h0 j
  | succ i =>
    cases j using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hij).elim
    | succ j =>
      have hij' : i < j := Fin.succ_lt_succ_iff.mp hij
      let i' : Fin (n + 2) := i.castLT
        (Nat.lt_of_lt_of_le hij' (Nat.le_of_lt_succ j.isLt))
      let j' : Fin (n + 2) := j.pred (Fin.ne_zero_of_lt hij')
      have hi' : i'.castSucc = i := by apply Fin.ext; rfl
      have hleft : (i.succ).castLT
          (Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.succ.isLt)) = i'.succ := by
        apply Fin.ext; rfl
      have hj' : j'.succ = j := Fin.succ_pred _ _
      change c (ULift.up (a ≫ U.δ j)) ≫ U.δ ((i.succ).castLT _) =
        c (ULift.up (a ≫ U.δ i)) ≫ U.δ j
      rw [hleft, ← hj', hs, hs]
      apply congrArg b
      apply ULift.ext
      have he := U.δ_comp_δ' (i := i') (j := j) (by simpa only [hi'] using hij')
      simpa only [Category.assoc, hi', j', hj'] using congrArg (fun t ↦ a ≫ t) he

/-- Finite simplices in a hypercover admit compatible local cones.
Source: Stacks Project, Hypercoverings, Tag 01GE, finite-support contraction argument.
(auxiliary; not a blueprint node).

Proof: A map from a lower-dimensional simplex misses a vertex, so factor it through
that face. Two choices give the same component: factor through their common face
and use the face-pair equation. This constructs a compatible full matching family
from any compatible codimension-one tuple, and the hypercover hypothesis lifts it
locally. Finitely many such local conditions hold on the intersection of their
covering sieves.

For a finite family of edges, take its finite set of vertices. Choose one original
vertex in each augmentation fibre; these fibres already have vertices, so no local
choice in degree zero is needed. Lift the pairs (vertex, chosen base vertex) locally
to edges. For each original edge a, the tuple consisting of a and the two chosen
vertex cones is a compatible triangle boundary. Lift these triangles on a common
refinement. They give the first pair of cone functions.

Induct on dimension. Apply the previous case to the finite set of faces of the
original family. Over each member of its covering, prescribe the new cone's zeroth
face to be the original simplex and its other faces to be the already chosen face
cones. Their face-pair equations follow from the previous cone equations and the
simplicial face identity. The augmentation equations follow from the zeroth-face
equations. Lift this finite family of boundaries on a common covering refinement.
Compose this refinement with the preceding covering by sieve binding and
transitivity. Retain the two adjacent cone functions; extend outside the finite
sets by one of the already chosen values. Nonemptiness ensures these defaults
exist. All functions are indexed by the original labels before restriction. -/
theorem finite_local_cones (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (hcover : HasLocalLifts J W U e) (n : ℕ) (T : C)
    (A : Finset (ULift.{v} (T ⟶ U _⦋n + 1⦌))) (hA : A.Nonempty) :
    ∃ K : Sieve T, K ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), K f →
      ∃ (c : ULift.{v} (T ⟶ U _⦋n + 1⦌) → (V ⟶ U _⦋n + 2⦌))
        (b : ULift.{v} (T ⟶ U _⦋n⦌) → (V ⟶ U _⦋n + 1⦌)),
        ∀ a ∈ A, c a ≫ U.δ 0 = f ≫ a.down ∧
          ∀ i : Fin (n + 2), c a ≫ U.δ i.succ = b (ULift.up (a.down ≫ U.δ i)) := by
  classical
  induction n generalizing T with
  | zero => exact finite_local_cones_zero J W U e hcover T A hA
  | succ n ih =>
    let B := A.biUnion (fun a ↦ Finset.univ.image
      (fun i : Fin (n + 3) ↦
        (ULift.up (a.down ≫ U.δ i) : ULift.{v} (T ⟶ U _⦋n + 1⦌))))
    have hB (a : ULift.{v} (T ⟶ U _⦋n + 2⦌)) (ha : a ∈ A) (i : Fin (n + 3)) :
        ULift.up (a.down ≫ U.δ i) ∈ B := by
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hBne : B.Nonempty := ⟨_, hB hA.choose hA.choose_spec 0⟩
    obtain ⟨K, hKmem, hK⟩ := ih T B hBne
    have hrefine (V : C) (f : V ⟶ T) (hf : K f) :
        ∃ Q : Sieve V, Q ∈ J V ∧ ∀ (Z : C) (g : Z ⟶ V), Q g →
          ∃ (c : ULift.{v} (T ⟶ U _⦋n + 2⦌) → (Z ⟶ U _⦋n + 3⦌))
            (b : ULift.{v} (T ⟶ U _⦋n + 1⦌) → (Z ⟶ U _⦋n + 2⦌)),
            ∀ a ∈ A, c a ≫ U.δ 0 = (g ≫ f) ≫ a.down ∧
              ∀ i : Fin (n + 3), c a ≫ U.δ i.succ = b (ULift.up (a.down ≫ U.δ i)) := by
      obtain ⟨oldc, oldb, hold⟩ := hK V f hf
      let faces (a : ULift.{v} (T ⟶ U _⦋n + 2⦌)) : Fin (n + 4) → (V ⟶ U _⦋n + 2⦌) :=
        Fin.cases (f ≫ a.down) (fun i ↦ oldc (ULift.up (a.down ≫ U.δ i)))
      have hcompat (a : ULift.{v} (T ⟶ U _⦋n + 2⦌)) (ha : a ∈ A) :=
        cone_faces_compatible U n T V f a.down oldc oldb
          (fun i ↦ by simpa only [Category.assoc] using (hold _ (hB a ha i)).1)
          (fun i j ↦ (hold _ (hB a ha i)).2 j)
      have haug (a : ULift.{v} (T ⟶ U _⦋n + 2⦌)) (ha : a ∈ A) (i : Fin (n + 4)) :
          faces a i ≫ e.app (op ⦋n + 2⦌) = f ≫ a.down ≫ e.app (op ⦋n + 2⦌) := by
        have he (j : Fin (n + 3)) : U.δ j ≫ e.app (op ⦋n + 1⦌) = e.app (op ⦋n + 2⦌) :=
          (e.naturality (SimplexCategory.δ j).op).trans (Category.comp_id _)
        cases i using Fin.cases with
        | zero => exact Category.assoc _ _ _
        | succ i =>
          change oldc _ ≫ e.app (op ⦋n + 2⦌) = _
          rw [← he 0, ← Category.assoc, (hold _ (hB a ha i)).1]
          simp only [Category.assoc, he]
      obtain ⟨Q, hQ, hc⟩ := finite_local_lifts J V A hA (fun Z ↦ Z ⟶ U _⦋n + 3⦌)
        (fun a Z g c ↦ ∀ i : Fin (n + 4), c ≫ U.δ i = g ≫ faces a i)
        (fun a ha ↦ local_face_lift J W U e hcover (n + 1) V
          (f ≫ a.down ≫ e.app (op ⦋n + 2⦌)) (faces a) (hcompat a ha) (haug a ha))
      refine ⟨Q, hQ, fun Z g hg ↦ ?_⟩
      obtain ⟨c, hc⟩ := hc Z g hg
      refine ⟨c, fun a ↦ g ≫ oldc a, fun a ha ↦ ?_⟩
      refine ⟨?_, fun i ↦ ?_⟩
      · simpa only [faces, Fin.cases_zero, Category.assoc] using hc a ha 0
      · simpa only [faces, Fin.cases_succ] using hc a ha i.succ
    choose Q hQ hprop using hrefine
    refine ⟨Sieve.bind K (fun {V} {f} hf ↦ Q V f hf),
      J.bind_covering hKmem (fun V f hf ↦ hQ V f hf), fun Z h hh ↦ ?_⟩
    obtain ⟨V, g, f, hf, hg, rfl⟩ := hh
    exact hprop V f hf Z g hg


end CategoryTheory.RingedHypercover
