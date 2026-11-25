/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.TraceSplitting
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

/-!
# Averaging over subgroups in a preadditive category

Let `V` be an object of a preadditive category with an action `ρ : G → End V` of a finite group
(`ρ a ≫ ρ b = ρ (b * a)`, `ρ 1 = 𝟙`) such that `|G|` is invertible on `V`. For a subgroup `H`,
the *average* `avg_H = |H|⁻¹ ∑_{a ∈ H} ρ a` (`CategoryTheory.subgroupAvg`, written as
`[G : H] |G|⁻¹ ∑_{a ∈ H} ρ a` so that only `|G|` needs to be invertible) is the projector onto
the `H`-invariants:

* a morphism to (resp. from) `V` invariant under `H` is fixed by `avg_H`
  (`CategoryTheory.comp_subgroupAvg_of_forall`, `CategoryTheory.subgroupAvg_comp_of_forall`);
* `avg_⊥ = 𝟙`, `avg_⊤ = |G|⁻¹ ∑_a ρ a`;
* `avg_A ≫ avg_B = avg_(A ⊔ B)` for `B` normal (`CategoryTheory.subgroupAvg_comp_subgroupAvg`);
* if `(i, n) ↦ c i * n` is a bijection `I × H ≃ G`, then `avg_H ≫ ∑_i ρ (c i) = |I| • avg_⊤`
  (`CategoryTheory.subgroupAvg_comp_sum`).
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {G : Type*} [Group G] [Fintype G]

/-- The inverse of multiplication by an integer is natural. -/
lemma inv_nsmul_id_comp {A B : C} (n : ℕ) [IsIso (n • 𝟙 A)] [IsIso (n • 𝟙 B)] (f : A ⟶ B) :
    inv (n • 𝟙 A) ≫ f = f ≫ inv (n • 𝟙 B) := by
  rw [IsIso.inv_comp_eq, nsmul_comp, id_comp, ← comp_nsmul, nsmul_inv_nsmul_id, comp_id]

/-- The inverse of multiplication by `n` only depends on `n`. -/
lemma inv_nsmul_id_congr {A : C} {n m : ℕ} (h : n = m) [IsIso (n • 𝟙 A)] [IsIso (m • 𝟙 A)] :
    inv (n • 𝟙 A) = inv (m • 𝟙 A) := by
  subst h
  rfl

variable {V : C} (ρ : G → (V ⟶ V))

open scoped Classical in
/-- The sum `∑_{a ∈ H} ρ a` over a subgroup. -/
noncomputable def subgroupSum (H : Subgroup G) : V ⟶ V :=
  ∑ a : H, ρ a

/-- The average `[G : H] |G|⁻¹ ∑_{a ∈ H} ρ a = |H|⁻¹ ∑_{a ∈ H} ρ a` over a subgroup. -/
noncomputable def subgroupAvg [IsIso (Nat.card G • 𝟙 V)] (H : Subgroup G) : V ⟶ V :=
  (Nat.card G / Nat.card H) • (inv (Nat.card G • 𝟙 V) ≫ subgroupSum ρ H)

variable {ρ} (hρ : ∀ a b, ρ a ≫ ρ b = ρ (b * a))
include hρ

/-- The sum over `H` is invariant under `H` on the right. -/
lemma subgroupSum_comp {H : Subgroup G} {a : G} (ha : a ∈ H) :
    subgroupSum ρ H ≫ ρ a = subgroupSum ρ H := by
  classical
  simp only [subgroupSum, sum_comp, hρ]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : H)) _ _ fun _ ↦ rfl

/-- The sum over `H` is invariant under `H` on the left. -/
lemma comp_subgroupSum {H : Subgroup G} {a : G} (ha : a ∈ H) :
    ρ a ≫ subgroupSum ρ H = subgroupSum ρ H := by
  classical
  simp only [subgroupSum, comp_sum, hρ]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : H)) _ _ fun _ ↦ rfl

/-- The sum over a normal subgroup commutes with the action. -/
lemma subgroupSum_comp_comm {H : Subgroup G} (hH : H.Normal) (a : G) :
    subgroupSum ρ H ≫ ρ a = ρ a ≫ subgroupSum ρ H := by
  classical
  simp only [subgroupSum, sum_comp, comp_sum, hρ]
  refine Fintype.sum_equiv (show H ≃ H from
    { toFun b := ⟨a * (b : G) * a⁻¹, hH.conj_mem _ b.2 a⟩
      invFun b := ⟨a⁻¹ * (b : G) * a, by simpa using hH.conj_mem _ b.2 a⁻¹⟩
      left_inv b := Subtype.ext (by simp [mul_assoc])
      right_inv b := Subtype.ext (by simp [mul_assoc]) }) _ _ fun b ↦ ?_
  exact congrArg ρ (by simp [mul_assoc])

variable [IsIso (Nat.card G • 𝟙 V)]

omit hρ in
/-- Unfolding the average. -/
lemma subgroupAvg_eq (H : Subgroup G) :
    subgroupAvg ρ H = (Nat.card G / Nat.card H) • (inv (Nat.card G • 𝟙 V) ≫ subgroupSum ρ H) :=
  rfl

omit hρ in
/-- A morphism to `V` invariant under `H` is fixed by the average over `H`. -/
lemma comp_subgroupAvg_of_forall {H : Subgroup G} {W : C} (x : W ⟶ V)
    (hx : ∀ a ∈ H, x ≫ ρ a = x) : x ≫ subgroupAvg ρ H = x := by
  have hS : x ≫ subgroupSum ρ H = Nat.card H • x := by
    classical
    simp only [subgroupSum, comp_sum]
    rw [Finset.sum_congr rfl fun a _ ↦ hx a.1 a.2, Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  rw [subgroupAvg, comp_nsmul, inv_nsmul_id_comp, ← assoc, hS, nsmul_comp, smul_smul,
    Nat.div_mul_cancel (Subgroup.card_subgroup_dvd_card H), ← comp_nsmul,
    nsmul_inv_nsmul_id, comp_id]

omit hρ in
/-- A morphism from `V` invariant under `H` is fixed by the average over `H`. -/
lemma subgroupAvg_comp_of_forall {H : Subgroup G} {W : C} (y : V ⟶ W)
    (hy : ∀ a ∈ H, ρ a ≫ y = y) : subgroupAvg ρ H ≫ y = y := by
  have hS : subgroupSum ρ H ≫ y = Nat.card H • y := by
    classical
    simp only [subgroupSum, sum_comp]
    rw [Finset.sum_congr rfl fun a _ ↦ hy a.1 a.2, Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  rw [subgroupAvg, nsmul_comp, assoc, hS, comp_nsmul, smul_smul,
    Nat.div_mul_cancel (Subgroup.card_subgroup_dvd_card H), ← nsmul_comp,
    nsmul_inv_nsmul_id, id_comp]

/-- The average over `H` is invariant under `H` on the right. -/
lemma subgroupAvg_comp {H : Subgroup G} {a : G} (ha : a ∈ H) :
    subgroupAvg ρ H ≫ ρ a = subgroupAvg ρ H := by
  rw [subgroupAvg, nsmul_comp, assoc, subgroupSum_comp hρ ha]

/-- The average over `H` is invariant under `H` on the left. -/
lemma comp_subgroupAvg {H : Subgroup G} {a : G} (ha : a ∈ H) :
    ρ a ≫ subgroupAvg ρ H = subgroupAvg ρ H := by
  rw [subgroupAvg, comp_nsmul, ← assoc, ← inv_nsmul_id_comp, assoc, comp_subgroupSum hρ ha]

/-- The average over a normal subgroup commutes with the action. -/
lemma subgroupAvg_comp_comm {H : Subgroup G} (hH : H.Normal) (a : G) :
    subgroupAvg ρ H ≫ ρ a = ρ a ≫ subgroupAvg ρ H := by
  rw [subgroupAvg, nsmul_comp, comp_nsmul, assoc, subgroupSum_comp_comm hρ hH, ← assoc, ← assoc,
    ← inv_nsmul_id_comp]

omit hρ in
/-- The average over the trivial subgroup is the identity. -/
lemma subgroupAvg_bot (hρ1 : ρ 1 = 𝟙 V) : subgroupAvg ρ ⊥ = 𝟙 V := by
  classical
  have : subgroupSum ρ (⊥ : Subgroup G) = 𝟙 V := by
    rw [subgroupSum]
    convert (Fintype.sum_eq_single (f := fun a : (⊥ : Subgroup G) ↦ ρ a)
      (⟨1, one_mem _⟩ : (⊥ : Subgroup G))
      fun b hb ↦ absurd (Subsingleton.elim b _) hb).trans hρ1
  rw [subgroupAvg, this, Subgroup.card_bot, Nat.div_one, comp_id, nsmul_inv_nsmul_id]

omit hρ in
/-- The average over the whole group is `|G|⁻¹ ∑_a ρ a`. -/
lemma subgroupAvg_top : subgroupAvg ρ ⊤ = inv (Nat.card G • 𝟙 V) ≫ ∑ a, ρ a := by
  classical
  have : subgroupSum ρ (⊤ : Subgroup G) = ∑ a, ρ a :=
    Fintype.sum_equiv Subgroup.topEquiv.toEquiv (fun a : (⊤ : Subgroup G) ↦ ρ a) ρ fun _ ↦ rfl
  rw [subgroupAvg, this, Subgroup.card_top, Nat.div_self Nat.card_pos, one_smul]

/-- **Product of averages**: for `B` normal, `avg_A ≫ avg_B = avg_(A ⊔ B)`. -/
lemma subgroupAvg_comp_subgroupAvg (hρ1 : ρ 1 = 𝟙 V) (A B : Subgroup G) (hB : B.Normal) :
    subgroupAvg ρ A ≫ subgroupAvg ρ B = subgroupAvg ρ (A ⊔ B) := by
  set x := subgroupAvg ρ A ≫ subgroupAvg ρ B
  let S : Subgroup G :=
    { carrier := {c | x ≫ ρ c = x}
      one_mem' := by
        change x ≫ ρ 1 = x
        rw [hρ1, comp_id]
      mul_mem' := fun {c d} hc hd ↦ by
        change x ≫ ρ c = x at hc
        change x ≫ ρ d = x at hd
        change x ≫ ρ (c * d) = x
        rw [← hρ d c, ← assoc, hd, hc]
      inv_mem' := fun {c} hc ↦ by
        change x ≫ ρ c = x at hc
        change x ≫ ρ c⁻¹ = x
        conv_lhs => rw [← hc]
        rw [assoc, hρ, inv_mul_cancel, hρ1, comp_id] }
  have hS : A ⊔ B ≤ S := sup_le (fun a ha ↦ by
      change x ≫ ρ a = x
      rw [assoc, subgroupAvg_comp_comm hρ hB, ← assoc, subgroupAvg_comp hρ ha])
    fun b hb ↦ by
      change x ≫ ρ b = x
      rw [assoc, subgroupAvg_comp hρ hb]
  rw [← comp_subgroupAvg_of_forall x fun c hc ↦ hS hc, assoc,
    subgroupAvg_comp_of_forall _ fun b hb ↦ comp_subgroupAvg hρ (le_sup_right (a := A) hb),
    subgroupAvg_comp_of_forall _ fun a ha ↦ comp_subgroupAvg hρ (le_sup_left (b := B) ha)]

/-- **Averaging over coset representatives**: if `(i, n) ↦ c i * n` is a bijection
`I × H → G`, then `avg_H ≫ ∑_i ρ (c i) = |I| • avg_⊤`. -/
lemma subgroupAvg_comp_sum {H : Subgroup G} {I : Type*} [Fintype I] (c : I → G)
    (hc : Function.Bijective fun x : I × H ↦ c x.1 * x.2) :
    subgroupAvg ρ H ≫ ∑ i, ρ (c i) = Nat.card I • subgroupAvg ρ ⊤ := by
  have hsum : subgroupSum ρ H ≫ ∑ i, ρ (c i) = ∑ g, ρ g := by
    classical
    simp only [subgroupSum, sum_comp, comp_sum, hρ]
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_bijective _ hc (fun x : I × H ↦ ρ (c x.1 * x.2)) ρ fun _ ↦ rfl
  have hcard : Nat.card G = Nat.card I * Nat.card H := by
    rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective _ hc)]
  rw [subgroupAvg, nsmul_comp, assoc, hsum, subgroupAvg_top,
    Nat.div_eq_of_eq_mul_left Nat.card_pos hcard]

end CategoryTheory
