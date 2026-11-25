/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Tactic

/-!
# An explicit ordinal path construction

The ordered join of two copies of `[n]` gives a simplicial object with two endpoint
maps and their canonical homotopy. This is the finite-simplex version of the endpoint
construction in Stacks, Tags 01GN and 01GS.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SimplexCategory.OrdinalPath

/-- The ordered join of two copies of an ordinal. -/
def obj (n : SimplexCategory) : SimplexCategory := ⦋2 * n.len + 1⦌

/-- Apply a monotone map on each of the two blocks. -/
def map {n m : SimplexCategory} (f : n ⟶ m) : obj n ⟶ obj m :=
  Hom.mk
    { toFun := fun i ↦ if h : i.val ≤ n.len then
        ⟨(f.toOrderHom ⟨i.val, by omega⟩).val, by
          have := (f.toOrderHom ⟨i.val, by omega⟩).isLt
          dsimp [obj]
          omega⟩
      else
        ⟨m.len + 1 + (f.toOrderHom ⟨i.val - (n.len + 1), by
          have := i.isLt
          dsimp [obj] at this
          omega⟩).val, by
          have := (f.toOrderHom ⟨i.val - (n.len + 1), by
            have := i.isLt
            dsimp [obj] at this
            omega⟩).isLt
          dsimp [obj]
          omega⟩
      monotone' := by
        intro i j hij
        dsimp only
        split_ifs with hi hj hj
        · exact f.toOrderHom.monotone (by exact hij)
        · have := (f.toOrderHom ⟨i.val, by omega⟩).isLt
          simp only [Fin.le_def]
          omega
        · simp only [Fin.le_def] at hij
          omega
        · simp only [Fin.le_def]
          apply Nat.add_le_add_left
          exact f.toOrderHom.monotone (by simp only [Fin.le_def]; omega) }

@[simp]
lemma map_apply_left {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (map f).toOrderHom ⟨i.val, by dsimp [obj]; omega⟩ =
      ⟨(f.toOrderHom i).val, by have := (f.toOrderHom i).isLt; dsimp [obj]; omega⟩ := by
  simp [map, show i.val ≤ n.len by omega]

@[simp]
lemma map_apply_right {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (map f).toOrderHom ⟨n.len + 1 + i.val, by dsimp [obj]; omega⟩ =
      ⟨m.len + 1 + (f.toOrderHom i).val, by
        have := (f.toOrderHom i).isLt
        dsimp [obj]
        omega⟩ := by
  simp [map, show ¬n.len + 1 + i.val ≤ n.len by omega]

/-- Doubling an ordinal functorially by ordered join. -/
def doubling : SimplexCategory ⥤ SimplexCategory where
  obj := obj
  map := map
  map_id n := by
    apply Hom.ext
    apply DFunLike.ext
    intro i
    apply Fin.ext
    dsimp [map]
    split_ifs
    · rfl
    · change n.len + 1 + (i.val - (n.len + 1)) = i.val
      omega
  map_comp {n m l} f g := by
    apply Hom.ext
    apply DFunLike.ext
    intro i
    by_cases h : i.val ≤ n.len
    · let j : Fin (n.len + 1) := ⟨i.val, by omega⟩
      have e : i = ⟨j.val, by dsimp [obj]; omega⟩ := rfl
      rw [e]
      change (map (f ≫ g)).toOrderHom ⟨j.val, _⟩ =
        (map g).toOrderHom ((map f).toOrderHom ⟨j.val, _⟩)
      simp only [map_apply_left]
      rfl
    · have hi := i.isLt
      dsimp [obj] at hi
      let j : Fin (n.len + 1) := ⟨i.val - (n.len + 1), by omega⟩
      have e : i = ⟨n.len + 1 + j.val, by dsimp [obj]; omega⟩ := by
        apply Fin.ext
        dsimp [j]
        omega
      rw [e]
      change (map (f ≫ g)).toOrderHom ⟨n.len + 1 + j.val, _⟩ =
        (map g).toOrderHom ((map f).toOrderHom ⟨n.len + 1 + j.val, _⟩)
      simp only [map_apply_right]
      rfl

/-- First endpoint inclusion. -/
def left (n : SimplexCategory) : n ⟶ obj n :=
  Hom.mk { toFun := fun i ↦ ⟨i.val, by dsimp [obj]; omega⟩
           monotone' := fun _ _ h ↦ h }

/-- Second endpoint inclusion. -/
def right (n : SimplexCategory) : n ⟶ obj n :=
  Hom.mk { toFun := fun i ↦ ⟨n.len + 1 + i.val, by dsimp [obj]; omega⟩
           monotone' := fun _ _ h ↦ Nat.add_le_add_left h _ }

lemma left_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    left n ≫ map f = f ≫ left m := by
  ext i
  exact congrArg Fin.val (map_apply_left f i)

lemma right_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    right n ≫ map f = f ≫ right m := by
  ext i
  exact congrArg Fin.val (map_apply_right f i)

/-- A cut takes the first vertices in the first block and the rest in the second block. -/
def cut {n : ℕ} (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ obj ⦋n⦌ :=
  Hom.mk
    { toFun := fun j ↦ if h : j.val ≤ i.val then
        ⟨j.val, by dsimp [obj]; have := i.isLt; omega⟩
      else ⟨n + j.val, by
        have hj : j.val < n + 1 + 1 := j.isLt
        dsimp [obj]
        omega⟩
      monotone' := by
        intro j k hjk
        dsimp only
        split_ifs <;> simp only [Fin.le_def] at * <;> omega }

lemma cut_val {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    ((cut i).toOrderHom j).val = if j.val ≤ i.val then j.val else n + j.val := by
  dsimp [cut]
  split_ifs <;> rfl

private lemma δ_val {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((δ i).toOrderHom j).val = if j.val < i.val then j.val else j.val + 1 := by
  change (i.succAbove j).val = _
  by_cases h : j.val < i.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by exact Nat.le_of_not_gt h)]
    simp [h]

private lemma σ_val {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    ((σ i).toOrderHom j).val = if i.val < j.val then j.val - 1 else j.val := by
  change (i.predAbove j).val = _
  by_cases h : i.val < j.val
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by exact h)]
    simp [h]
  · rw [Fin.predAbove_of_le_castSucc _ _ (by exact Nat.le_of_not_gt h)]
    simp [h]

lemma map_val {n m : SimplexCategory} (f : n ⟶ m) (i : Fin ((obj n).len + 1)) :
    ((map f).toOrderHom i).val = if h : i.val ≤ n.len then
        (f.toOrderHom ⟨i.val, by omega⟩).val
      else m.len + 1 + (f.toOrderHom ⟨i.val - (n.len + 1), by
        have hi : i.val < 2 * n.len + 1 + 1 := i.isLt
        omega⟩).val := by
  dsimp [map]
  split_ifs <;> rfl

lemma δ_zero_cut (n : ℕ) : δ 0 ≫ cut (0 : Fin (n + 1)) = right ⦋n⦌ := by
  apply Hom.ext
  apply DFunLike.ext
  intro j
  apply Fin.ext
  simp [δ, cut, right]
  omega

lemma δ_last_cut (n : ℕ) :
    δ (Fin.last (n + 1)) ≫ cut (Fin.last n) = left ⦋n⦌ := by
  apply Hom.ext
  apply DFunLike.ext
  intro j
  apply Fin.ext
  have hj : j.val < n + 1 := j.isLt
  simp [δ, cut, left, show j.val ≤ n by omega]

lemma δ_cut_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    δ i.castSucc ≫ cut j.succ = cut j ≫ map (δ i) := by
  apply Hom.ext
  apply DFunLike.ext
  intro k
  apply Fin.ext
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cut_val, map_val,
    δ_val, Fin.val_castSucc, Fin.val_succ, len_mk]
  split_ifs <;> (try simp_all only [Fin.val_castSucc, Fin.le_def]) <;> omega

lemma δ_cut_middle {n : ℕ} (j : Fin (n + 1)) :
    δ j.castSucc.succ ≫ cut j.succ = δ j.castSucc.succ ≫ cut j.castSucc := by
  apply Hom.ext
  apply DFunLike.ext
  intro k
  apply Fin.ext
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cut_val,
    δ_val, Fin.val_castSucc, Fin.val_succ, len_mk]
  split_ifs <;> omega

lemma δ_cut_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    δ i.succ ≫ cut j.castSucc = cut j ≫ map (δ i) := by
  apply Hom.ext
  apply DFunLike.ext
  intro k
  apply Fin.ext
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cut_val, map_val,
    δ_val, Fin.val_castSucc, Fin.val_succ, len_mk]
  split_ifs <;> (try simp_all only [Fin.val_castSucc, Fin.lt_def]) <;> omega

lemma σ_cut_of_le {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    σ i.castSucc ≫ cut j = cut j.succ ≫ map (σ i) := by
  apply Hom.ext
  apply DFunLike.ext
  intro k
  apply Fin.ext
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cut_val, map_val,
    σ_val, Fin.val_castSucc, Fin.val_succ, len_mk]
  split_ifs <;> (try simp_all only [Fin.le_def]) <;> omega

lemma σ_cut_of_ge {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    σ i.succ ≫ cut j = cut j.castSucc ≫ map (σ i) := by
  apply Hom.ext
  apply DFunLike.ext
  intro k
  apply Fin.ext
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cut_val, map_val,
    σ_val, Fin.val_castSucc, Fin.val_succ, len_mk]
  split_ifs <;> (try simp_all only [Fin.le_def]) <;> omega

end SimplexCategory.OrdinalPath

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

open SimplexCategory.OrdinalPath

/-- The degree `n` term is `V_(2n+1)`, with operators acting on both ordered blocks. -/
def ordinalPath (V : SimplicialObject C) : SimplicialObject C := doubling.op ⋙ V

/-- Restriction to the first block. -/
def ordinalPathLeft (V : SimplicialObject C) : ordinalPath V ⟶ V where
  app Δ := V.map (left Δ.unop).op
  naturality {Δ Δ'} f := by
    change V.map (map f.unop).op ≫ V.map (left Δ'.unop).op =
      V.map (left Δ.unop).op ≫ V.map f
    rw [← V.map_comp, ← V.map_comp]
    congr 1
    exact congrArg Quiver.Hom.op (left_naturality f.unop)

/-- Restriction to the second block. -/
def ordinalPathRight (V : SimplicialObject C) : ordinalPath V ⟶ V where
  app Δ := V.map (right Δ.unop).op
  naturality {Δ Δ'} f := by
    change V.map (map f.unop).op ≫ V.map (right Δ'.unop).op =
      V.map (right Δ.unop).op ≫ V.map f
    rw [← V.map_comp, ← V.map_comp]
    congr 1
    exact congrArg Quiver.Hom.op (right_naturality f.unop)

/-- The cuts in the ordered join give the canonical elementary simplicial homotopy. -/
def ordinalPathHomotopy (V : SimplicialObject C) :
    Homotopy (ordinalPathLeft V) (ordinalPathRight V) where
  h i := V.map (cut i).op
  h_zero_comp_δ_zero n := by
    change V.map (cut (0 : Fin (n + 1))).op ≫ V.map (SimplexCategory.δ 0).op = _
    rw [← V.map_comp]
    exact congrArg (fun f ↦ V.map f.op) (δ_zero_cut n)
  h_last_comp_δ_last n := by
    change V.map (cut (Fin.last n)).op ≫
      V.map (SimplexCategory.δ (Fin.last (n + 1))).op = _
    rw [← V.map_comp]
    exact congrArg (fun f ↦ V.map f.op) (δ_last_cut n)
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    change V.map (cut j.succ).op ≫ V.map (SimplexCategory.δ i.castSucc).op =
      V.map (map (SimplexCategory.δ i)).op ≫ V.map (cut j).op
    rw [← V.map_comp, ← V.map_comp]
    exact congrArg (fun f ↦ V.map f.op) (δ_cut_of_le i j hij)
  h_succ_comp_δ_castSucc_succ j := by
    change V.map (cut j.succ).op ≫ V.map (SimplexCategory.δ j.castSucc.succ).op =
      V.map (cut j.castSucc).op ≫ V.map (SimplexCategory.δ j.castSucc.succ).op
    rw [← V.map_comp, ← V.map_comp]
    exact congrArg (fun f ↦ V.map f.op) (δ_cut_middle j)
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    change V.map (cut j.castSucc).op ≫ V.map (SimplexCategory.δ i.succ).op =
      V.map (map (SimplexCategory.δ i)).op ≫ V.map (cut j).op
    rw [← V.map_comp, ← V.map_comp]
    exact congrArg (fun f ↦ V.map f.op) (δ_cut_of_lt i j hji)
  h_comp_σ_castSucc_of_le i j hij := by
    change V.map (cut j).op ≫ V.map (SimplexCategory.σ i.castSucc).op =
      V.map (map (SimplexCategory.σ i)).op ≫ V.map (cut j.succ).op
    rw [← V.map_comp, ← V.map_comp]
    exact congrArg (fun f ↦ V.map f.op) (σ_cut_of_le i j hij)
  h_comp_σ_succ_of_lt i j hji := by
    change V.map (cut j).op ≫ V.map (SimplexCategory.σ i.succ).op =
      V.map (map (SimplexCategory.σ i)).op ≫ V.map (cut j.castSucc).op
    rw [← V.map_comp, ← V.map_comp]
    exact congrArg (fun f ↦ V.map f.op) (σ_cut_of_ge i j hji)

section Pullback

variable [HasPullbacks C] [HasBinaryProducts C]

/-- The explicit endpoint pullback for two maps of simplicial objects. -/
noncomputable def ordinalPathPullback {U V : SimplicialObject C} (a b : U ⟶ V) :
    SimplicialObject C :=
  pullback (prod.lift a b) (prod.lift (ordinalPathLeft V) (ordinalPathRight V))

/-- Projection from the endpoint pullback to the source. -/
noncomputable def ordinalPathPullbackFst {U V : SimplicialObject C} (a b : U ⟶ V) :
    ordinalPathPullback a b ⟶ U := pullback.fst _ _

/-- Projection from the endpoint pullback to the ordered path object. -/
noncomputable def ordinalPathPullbackSnd {U V : SimplicialObject C} (a b : U ⟶ V) :
    ordinalPathPullback a b ⟶ ordinalPath V := pullback.snd _ _

lemma ordinalPathPullback_left {U V : SimplicialObject C} (a b : U ⟶ V) :
    ordinalPathPullbackFst a b ≫ a = ordinalPathPullbackSnd a b ≫ ordinalPathLeft V := by
  have h := pullback.condition (f := prod.lift a b)
    (g := prod.lift (ordinalPathLeft V) (ordinalPathRight V)) =≫ prod.fst
  simpa only [ordinalPathPullbackFst, ordinalPathPullbackSnd, ordinalPathPullback,
    Category.assoc, prod.lift_fst] using h

lemma ordinalPathPullback_right {U V : SimplicialObject C} (a b : U ⟶ V) :
    ordinalPathPullbackFst a b ≫ b = ordinalPathPullbackSnd a b ≫ ordinalPathRight V := by
  have h := pullback.condition (f := prod.lift a b)
    (g := prod.lift (ordinalPathLeft V) (ordinalPathRight V)) =≫ prod.snd
  simpa only [ordinalPathPullbackFst, ordinalPathPullbackSnd, ordinalPathPullback,
    Category.assoc, prod.lift_snd] using h

/-- The canonical homotopy on the explicitly constructed endpoint pullback.
Source: Stacks, Tag 01GS, endpoint pullback step; the ordered-simplex formulas above
supply the homotopy without invoking any existence theorem.
(auxiliary; not a blueprint node) -/
noncomputable def ordinalPathPullbackHomotopy {U V : SimplicialObject C} (a b : U ⟶ V) :
    Homotopy (ordinalPathPullbackFst a b ≫ a) (ordinalPathPullbackFst a b ≫ b) := by
  rw [ordinalPathPullback_left, ordinalPathPullback_right]
  exact (ordinalPathHomotopy V).precomp (ordinalPathPullbackSnd a b)

/-- Evaluation preserves the universal property of the endpoint pullback. -/
theorem ordinalPathPullback_lift_degree {U V : SimplicialObject C} (a b : U ⟶ V)
    (n : ℕ) {T : C} (u : T ⟶ U.obj (op ⦋n⦌))
    (v : T ⟶ V.obj (op ⦋2 * n + 1⦌))
    (hl : u ≫ a.app (op ⦋n⦌) = v ≫ V.map (left ⦋n⦌).op)
    (hr : u ≫ b.app (op ⦋n⦌) = v ≫ V.map (right ⦋n⦌).op) :
    ∃ k : T ⟶ (ordinalPathPullback a b).obj (op ⦋n⦌),
      k ≫ (ordinalPathPullbackFst a b).app (op ⦋n⦌) = u ∧
      k ≫ (ordinalPathPullbackSnd a b).app (op ⦋n⦌) = v := by
  let E := (evaluation _ C).obj (op ⦋n⦌)
  have he : u ≫ (prod.lift a b).app (op ⦋n⦌) =
      v ≫ (prod.lift (ordinalPathLeft V) (ordinalPathRight V)).app (op ⦋n⦌) := by
    apply BinaryFan.IsLimit.hom_ext (isLimitOfHasBinaryProductOfPreservesLimit E V V)
    · change (u ≫ (prod.lift a b).app (op ⦋n⦌)) ≫ (prod.fst : V ⨯ V ⟶ V).app (op ⦋n⦌) =
        (v ≫ (prod.lift (ordinalPathLeft V) (ordinalPathRight V)).app (op ⦋n⦌)) ≫
          (prod.fst : V ⨯ V ⟶ V).app (op ⦋n⦌)
      simpa only [Category.assoc, ← NatTrans.comp_app, prod.lift_fst, ordinalPathLeft] using hl
    · change (u ≫ (prod.lift a b).app (op ⦋n⦌)) ≫ (prod.snd : V ⨯ V ⟶ V).app (op ⦋n⦌) =
        (v ≫ (prod.lift (ordinalPathLeft V) (ordinalPathRight V)).app (op ⦋n⦌)) ≫
          (prod.snd : V ⨯ V ⟶ V).app (op ⦋n⦌)
      simpa only [Category.assoc, ← NatTrans.comp_app, prod.lift_snd, ordinalPathRight] using hr
  let h := (IsPullback.of_hasPullback (prod.lift a b)
    (prod.lift (ordinalPathLeft V) (ordinalPathRight V))).map E
  exact ⟨h.lift u v he, h.lift_fst u v he, h.lift_snd u v he⟩

/-- The two projections determine a map into each degree of the endpoint pullback. -/
theorem ordinalPathPullback_hom_ext_degree {U V : SimplicialObject C} (a b : U ⟶ V)
    (n : ℕ) {T : C} {f g : T ⟶ (ordinalPathPullback a b).obj (op ⦋n⦌)}
    (h₁ : f ≫ (ordinalPathPullbackFst a b).app (op ⦋n⦌) =
      g ≫ (ordinalPathPullbackFst a b).app (op ⦋n⦌))
    (h₂ : f ≫ (ordinalPathPullbackSnd a b).app (op ⦋n⦌) =
      g ≫ (ordinalPathPullbackSnd a b).app (op ⦋n⦌)) : f = g :=
  ((IsPullback.of_hasPullback (prod.lift a b)
    (prod.lift (ordinalPathLeft V) (ordinalPathRight V))).map
      ((evaluation _ C).obj (op ⦋n⦌))).hom_ext h₁ h₂

end Pullback

end CategoryTheory.SimplicialObject
