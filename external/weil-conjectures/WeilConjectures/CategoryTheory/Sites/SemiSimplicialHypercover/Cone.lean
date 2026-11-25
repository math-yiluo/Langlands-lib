/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Basic

/-!
# Local cones on hypercovers

Let `U` be a semi-simplicial object of a category `C`, and `g : W' ⟶ W`. A *cone* along `g` on
a simplex `σ : W ⟶ U.obj n` consists of a vertex `v : W' ⟶ U.obj 0` and of simplices
`h σ' : W' ⟶ U.obj (m + 1)` for `σ'` running over `σ` and its iterated faces, such that
`h σ'` has last face `g ≫ σ'` and other faces `h (σ' ≫ δ_i)` (the vertex `v` in dimension `0`).
This is the combinatorial input for the exactness of the free resolution of a hypercover: on
chains supported on simplices with a cone, `h` is a contracting homotopy.

The main result `CategoryTheory.SemiSimplicialObject.IsHypercover.coneSieve_mem` states that if
`U` is a hypercover of a site `(C, J)`, then every finite set of simplices of `U` with values in
`W` admits a cone locally on `W`. It is proved by induction on the dimension: the cone on the
faces gives a compatible family `(h (σ ≫ δ_0), …, h (σ ≫ δ_n), g ≫ σ)`, which lifts locally to
an `(n + 1)`-simplex.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A finite family of covering sieves has a common covering refinement. -/
lemma exists_mem_forall_le_of_finset {ι : Type*} (s : Finset ι) {W : C} (S : ι → Sieve W)
    (hS : ∀ i ∈ s, S i ∈ J W) : ∃ T ∈ J W, ∀ i ∈ s, T ≤ S i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, J.top_mem W, by simp⟩
  | insert a s ha ih =>
    obtain ⟨T, hT, hTS⟩ := ih fun i hi ↦ hS i (Finset.mem_insert_of_mem hi)
    refine ⟨S a ⊓ T, J.intersection_covering (hS a (Finset.mem_insert_self a s)) hT,
      fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact inf_le_left
    · exact inf_le_right.trans (hTS i hi)

end GrothendieckTopology

namespace SemiSimplicialObject

variable {C : Type u} [Category.{v} C] (U : SemiSimplicialObject C)

section Cone

variable {W W' : C}

/-- `IsCone g v h m σ`: the partial function `h`, sending `m`-simplices of `U` with values in `W`
to `(m + 1)`-simplices with values in `W'`, is a cone with vertex `v` along `g : W' ⟶ W` on the
simplex `σ : W ⟶ U.obj m` and all its iterated faces: `h σ` is defined, its last face is
`g ≫ σ`, and its other faces are `h (σ ≫ δ_i)` (resp. `v` if `m = 0`). -/
def IsCone (g : W' ⟶ W) (v : W' ⟶ U.obj 0)
    (h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))) : ∀ m, (W ⟶ U.obj m) → Prop
  | 0, σ => ∃ y, h 0 σ = some y ∧ y ≫ U.δ 0 1 = g ≫ σ ∧ y ≫ U.δ 0 0 = v
  | m + 1, σ => ∃ y, h (m + 1) σ = some y ∧ y ≫ U.δ (m + 1) (Fin.last _) = g ≫ σ ∧
      ∀ i : Fin (m + 2), h m (σ ≫ U.δ m i) = some (y ≫ U.δ (m + 1) i.castSucc) ∧
        IsCone g v h m (σ ≫ U.δ m i)

variable {U}

/-- A cone is defined at its simplex, with last face the simplex. -/
lemma IsCone.exists_eq_some {g : W' ⟶ W} {v : W' ⟶ U.obj 0}
    {h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))} {m : ℕ} {σ : W ⟶ U.obj m}
    (hc : U.IsCone g v h m σ) :
    ∃ y, h m σ = some y ∧ y ≫ U.δ m (Fin.last (m + 1)) = g ≫ σ := by
  cases m with
  | zero => exact ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2.1⟩
  | succ m => exact ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2.1⟩

/-- Being a cone only depends on the values of `h` in dimensions `≤ m`. -/
lemma IsCone.congr {g : W' ⟶ W} {v : W' ⟶ U.obj 0}
    {h h' : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))} :
    ∀ {m : ℕ} {σ : W ⟶ U.obj m}, U.IsCone g v h m σ → (∀ l ≤ m, h l = h' l) →
      U.IsCone g v h' m σ
  | 0, σ, ⟨y, hy, h₁, h₀⟩, hh => ⟨y, by rw [← hh 0 le_rfl, hy], h₁, h₀⟩
  | m + 1, σ, ⟨y, hy, hl, hf⟩, hh =>
    ⟨y, by rw [← hh (m + 1) le_rfl, hy], hl, fun i ↦
      ⟨by rw [← hh m (Nat.le_succ m), (hf i).1],
        (hf i).2.congr fun l hl ↦ hh l (hl.trans (Nat.le_succ m))⟩⟩

/-- Cones can be pulled back along morphisms `g' : W'' ⟶ W'`. -/
lemma IsCone.pullback {W'' : C} (g' : W'' ⟶ W') {g : W' ⟶ W} {v : W' ⟶ U.obj 0}
    {h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))} :
    ∀ {m : ℕ} {σ : W ⟶ U.obj m}, U.IsCone g v h m σ →
      U.IsCone (g' ≫ g) (g' ≫ v) (fun l τ ↦ (h l τ).map (g' ≫ ·)) m σ
  | 0, σ, ⟨y, hy, h₁, h₀⟩ =>
    ⟨g' ≫ y, by simp [hy], by simp [h₁], by simp [h₀]⟩
  | m + 1, σ, ⟨y, hy, hl, hf⟩ =>
    ⟨g' ≫ y, by simp [hy], by simp [hl], fun i ↦ ⟨by simp [(hf i).1], IsCone.pullback g' (hf i).2⟩⟩

/-- The faces `h (σ ≫ δ_i)` of a cone satisfy the simplicial identities among themselves. -/
lemma IsCone.getD_comp_δ {g : W' ⟶ W} {v : W' ⟶ U.obj 0}
    {h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))} {m : ℕ}
    {σ : W ⟶ U.obj (m + 1)} (hc : ∀ i, U.IsCone g v h m (σ ≫ U.δ m i)) (d : W' ⟶ U.obj (m + 1))
    {i j : Fin (m + 1)} (hij : i ≤ j) :
    (h m (σ ≫ U.δ m j.succ)).getD d ≫ U.δ m i.castSucc =
      (h m (σ ≫ U.δ m i.castSucc)).getD d ≫ U.δ m j.castSucc := by
  cases m with
  | zero =>
    obtain ⟨y, hy, -, hy₀⟩ := hc j.succ
    obtain ⟨y', hy', -, hy₀'⟩ := hc i.castSucc
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j] at *
    simp only [hy, hy', Option.getD_some]
    exact hy₀.trans hy₀'.symm
  | succ m =>
    obtain ⟨y, hy, -, hf⟩ := hc j.succ
    obtain ⟨y', hy', -, hf'⟩ := hc i.castSucc
    simp only [hy, hy', Option.getD_some]
    apply Option.some_injective
    rw [← (hf i).1, ← (hf' j).1, Category.assoc, Category.assoc, U.δ_comp_δ m hij]

variable (U) in
/-- The family `(h (σ ≫ δ_0), …, h (σ ≫ δ_m), g ≫ σ)` of a cone on the faces of `σ`. -/
def coneFamily (g : W' ⟶ W) (h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))) {m : ℕ}
    (σ : W ⟶ U.obj (m + 1)) : Fin (m + 3) → (W' ⟶ U.obj (m + 1)) :=
  Fin.lastCases (g ≫ σ) fun i ↦ (h m (σ ≫ U.δ m i)).getD (g ≫ σ)

@[simp]
lemma coneFamily_last (g : W' ⟶ W) (h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1)))
    {m : ℕ} (σ : W ⟶ U.obj (m + 1)) :
    U.coneFamily g h σ (Fin.last _) = g ≫ σ := by
  simp [coneFamily]

@[simp]
lemma coneFamily_castSucc (g : W' ⟶ W) (h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1)))
    {m : ℕ} (σ : W ⟶ U.obj (m + 1)) (i : Fin (m + 2)) :
    U.coneFamily g h σ i.castSucc = (h m (σ ≫ U.δ m i)).getD (g ≫ σ) := by
  simp [coneFamily]

/-- If `h` is a cone on the faces of `σ`, then `(h (σ ≫ δ_0), …, h (σ ≫ δ_m), g ≫ σ)` is a
compatible family. -/
lemma compatible_coneFamily {g : W' ⟶ W} {v : W' ⟶ U.obj 0}
    {h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))} {m : ℕ}
    {σ : W ⟶ U.obj (m + 1)} (hc : ∀ i, U.IsCone g v h m (σ ≫ U.δ m i)) :
    U.Compatible (U.coneFamily g h σ) := by
  rw [compatible_succ_iff]
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    obtain ⟨y, hy, hy'⟩ := (hc i).exists_eq_some
    simp only [Fin.succ_last, coneFamily_last, coneFamily_castSucc, hy, Option.getD_some, hy',
      Category.assoc]
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
    | cast i =>
      rw [Fin.succ_castSucc, coneFamily_castSucc, coneFamily_castSucc]
      exact IsCone.getD_comp_δ hc _ (Fin.castSucc_le_castSucc_iff.1 hij)

end Cone

/-- The sieve of the morphisms `g : W' ⟶ W` along which there is a cone on all the simplices of
the finite set `A`. -/
def coneSieve (n : ℕ) {W : C} (A : Finset (W ⟶ U.obj n)) : Sieve W where
  arrows W' g := ∃ (v : W' ⟶ U.obj 0) (h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))),
    ∀ σ ∈ A, U.IsCone g v h n σ
  downward_closed := by
    rintro W' W'' g ⟨v, h, hc⟩ g'
    exact ⟨g' ≫ v, _, fun σ hσ ↦ (hc σ hσ).pullback g'⟩

variable {U} {J : GrothendieckTopology C}

/-- **Local cones on hypercovers.** If `U` is a hypercover, every finite set of simplices of `U`
with values in `W` admits a cone locally on `W`. -/
theorem IsHypercover.coneSieve_mem (hU : U.IsHypercover J) :
    ∀ (n : ℕ) {W : C} (A : Finset (W ⟶ U.obj n)), U.coneSieve n A ∈ J W
  | 0, W, A => by
    classical
    refine J.transitive (hU.coverSieve_mem W) _ fun W' g hg ↦ ?_
    obtain ⟨v⟩ := hg
    let x : (W ⟶ U.obj 0) → Fin 2 → (W' ⟶ U.obj 0) := fun σ ↦ ![v, g ≫ σ]
    obtain ⟨T, hT, hTS⟩ := J.exists_mem_forall_le_of_finset A (fun σ ↦ U.liftSieve (x σ))
      fun σ _ ↦ hU.liftSieve_mem _ (U.compatible_zero _)
    refine J.superset_covering (fun W'' g' hg' ↦ ?_) hT
    have hy (σ : W ⟶ U.obj 0) (hσ : σ ∈ A) :
        ∃ y : W'' ⟶ U.obj (0 + 1), ∀ i, y ≫ U.δ 0 i = g' ≫ x σ i := hTS σ hσ _ hg'
    let k : (W ⟶ U.obj 0) → Option (W'' ⟶ U.obj (0 + 1)) := fun σ ↦
      if hσ : ∃ y : W'' ⟶ U.obj (0 + 1), ∀ i, y ≫ U.δ 0 i = g' ≫ x σ i then
        some hσ.choose else none
    refine ⟨g' ≫ v, Function.update (fun _ _ ↦ none) 0 k, fun σ hσ ↦ ?_⟩
    refine ⟨(hy σ hσ).choose,
      by simp only [Function.update_self, k, dite_eq_left (hy σ hσ)], ?_, ?_⟩
    · simpa [x] using (hy σ hσ).choose_spec 1
    · simpa [x] using (hy σ hσ).choose_spec 0
  | m + 1, W, A => by
    classical
    let B : Finset (W ⟶ U.obj m) := A.biUnion fun σ ↦ Finset.univ.image fun i ↦ σ ≫ U.δ m i
    refine J.transitive (hU.coneSieve_mem m B) _ fun W' g hg ↦ ?_
    obtain ⟨v, h, hc⟩ := hg
    have hc' (σ : W ⟶ U.obj (m + 1)) (hσ : σ ∈ A) (i : Fin (m + 2)) :
        U.IsCone g v h m (σ ≫ U.δ m i) :=
      hc _ (Finset.mem_biUnion.2 ⟨σ, hσ, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    obtain ⟨T, hT, hTS⟩ := J.exists_mem_forall_le_of_finset A
      (fun σ ↦ U.liftSieve (U.coneFamily g h σ))
      fun σ hσ ↦ hU.liftSieve_mem _ (compatible_coneFamily (hc' σ hσ))
    refine J.superset_covering (fun W'' g' hg' ↦ ?_) hT
    have hy (σ : W ⟶ U.obj (m + 1)) (hσ : σ ∈ A) :
        ∃ y : W'' ⟶ U.obj (m + 1 + 1), ∀ i, y ≫ U.δ (m + 1) i = g' ≫ U.coneFamily g h σ i :=
      hTS σ hσ _ hg'
    let k : (W ⟶ U.obj (m + 1)) → Option (W'' ⟶ U.obj (m + 1 + 1)) := fun σ ↦
      if hσ : ∃ y : W'' ⟶ U.obj (m + 1 + 1), ∀ i, y ≫ U.δ (m + 1) i = g' ≫ U.coneFamily g h σ i
      then some hσ.choose else none
    let h' := Function.update (fun l τ ↦ (h l τ).map (g' ≫ ·)) (m + 1) k
    have hh' (l : ℕ) (hl : l ≤ m) : (fun τ ↦ (h l τ).map (g' ≫ ·)) = h' l :=
      (Function.update_of_ne (show l ≠ m + 1 by lia) k fun l τ ↦ (h l τ).map (g' ≫ ·)).symm
    refine ⟨g' ≫ v, h', fun σ hσ ↦ ?_⟩
    refine ⟨(hy σ hσ).choose, by simp only [h', Function.update_self, k, dite_eq_left (hy σ hσ)],
      ?_, fun i ↦ ⟨?_, ?_⟩⟩
    · rw [(hy σ hσ).choose_spec, coneFamily_last, Category.assoc]
    · obtain ⟨z, hz, -⟩ := (hc' σ hσ i).exists_eq_some
      rw [← hh' m le_rfl, (hy σ hσ).choose_spec, coneFamily_castSucc, hz]
      simp [hz]
    · exact ((hc' σ hσ i).pullback g').congr hh'

end SemiSimplicialObject

end CategoryTheory
