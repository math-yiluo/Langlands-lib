/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups

/-!
# Vanishing of the first derived limit of an eventually constant tower

Source: Stacks Project, More on Algebra, Tag 07KW, and Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-limit-eventually-iso).
-/

@[expose] public section

universe u

open CategoryTheory.Limits CategoryTheory.Category

namespace CategoryTheory

attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

/-- A tower of abelian groups with eventually invertible successor transitions has
zero first right derived inverse limit.

Source: Stacks Project, Tag 07KW (lemma-Rlim), part (3), specialized to eventually
constant systems; Tag 08D4 (lemma-application-nice-K-injective), proof of (2)
(blueprint: lem-pc-derived-limit-eventually-iso).

Proof:
1. The Roos computation `lem-pc-derived-limit-roos-abelian-groups` identifies the
first right derived inverse limit with the cokernel of `1 - s` on the product.
2. Choose `m` after which all transitions `f n` are invertible. Given any tuple
`y`, set `x m = 0`. For `n ≥ m`, recursively put
`x (n + 1) = (f n)⁻¹ (x n - y n)`. For the finitely many indices below `m`,
recursively downwards put `x n = y n + f n (x (n + 1))`.
3. These equations give `x n - f n (x (n + 1)) = y n` at every index, including
`m = 0`, when the downward recursion is empty. Thus `1 - s` is surjective,
hence epic in abelian groups, and its cokernel is zero. Transport this zero
object along the Roos isomorphism. -/
theorem isZero_firstDerivedLimit_of_eventually_isIso
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      IsIso (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj A) := by
  classical
  obtain ⟨m, hm⟩ := hA
  let K : ℕ → AddCommGrpCat.{u} := fun n ↦ A.obj (Opposite.op n)
  let f : ∀ n : ℕ, K (n + 1) ⟶ K n := fun n ↦
    A.map (homOfLE (Nat.le_succ n)).op
  let P := ∏ᶜ K
  let up : ∀ z : ℤ, (m : ℤ) ≤ z → (P ⟶ K z.toNat) → (P ⟶ K (z + 1).toNat) :=
    fun z hz q ↦ by
      have : IsIso (f z.toNat) := hm z.toNat (by omega)
      have e : (z + 1).toNat = z.toNat + 1 := by omega
      exact (q - Pi.π K z.toNat) ≫ inv (f z.toNat) ≫ eqToHom (congrArg K e.symm)
  let down : ∀ z : ℤ, z ≤ (m : ℤ) → (P ⟶ K z.toNat) → (P ⟶ K (z - 1).toNat) :=
    fun z _ q ↦ if h : 0 < z then
      Pi.π K (z - 1).toNat + q ≫
        eqToHom (congrArg K (show (z - 1).toNat + 1 = z.toNat by omega).symm) ≫
          f (z - 1).toNat
    else 0
  let qInt : ∀ z : ℤ, P ⟶ K z.toNat := fun z ↦ z.inductionOn' (m : ℤ) 0 up down
  let q : ∀ n : ℕ, P ⟶ K n := fun n ↦ qInt n
  have hq : ∀ n : ℕ, q n - q (n + 1) ≫ f n = Pi.π K n := by
    intro n
    by_cases hn : m ≤ n
    · have he := Int.inductionOn'_add_one (motive := fun z : ℤ ↦ P ⟶ K z.toNat)
        (zero := (0 : P ⟶ K (m : ℤ).toNat)) (succ := up) (pred := down)
        (show (m : ℤ) ≤ (n : ℤ) by omega)
      have : IsIso (f n) := hm n hn
      dsimp [up] at he
      simp only [comp_id] at he
      change q (n + 1) = (q n - Pi.π K n) ≫ inv (f n) at he
      rw [he, assoc, IsIso.inv_hom_id, comp_id]
      abel
    · have he := Int.inductionOn'_sub_one (motive := fun z : ℤ ↦ P ⟶ K z.toNat)
        (zero := (0 : P ⟶ K (m : ℤ).toNat)) (succ := up) (pred := down)
        (show ((n + 1 : ℕ) : ℤ) ≤ (m : ℤ) by omega)
      dsimp [down] at he
      rw [dite_eq_left (show 0 < (n : ℤ) + 1 by omega)] at he
      rw! [show (n : ℤ) + 1 - 1 = (n : ℤ) by omega] at he
      simp only [eqToHom_refl] at he
      change q n = Pi.π K n + q (n + 1) ≫ f n at he
      rw [he]
      abel
  have hsplit : Pi.lift q ≫ roosMap A = 𝟙 P := by
    apply Pi.hom_ext
    intro n
    change (Pi.lift q ≫ (𝟙 P - towerProductShift f)) ≫ Pi.π K n =
      (𝟙 P) ≫ Pi.π K n
    dsimp only [P]
    simpa only [towerProductShift, Preadditive.comp_sub, Preadditive.sub_comp, assoc,
      id_comp, Pi.lift_comp_π, Pi.lift_comp_π_assoc] using hq n
  have : Epi (roosMap A) := epi_of_epi_fac hsplit
  obtain ⟨_, _, e₁, _⟩ := derivedLimitRoosAbelianGroups.{u}
  exact (isZero_cokernel_of_epi (roosMap A)).of_iso (e₁ A)

end CategoryTheory
