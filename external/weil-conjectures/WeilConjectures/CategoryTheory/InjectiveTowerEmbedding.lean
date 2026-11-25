/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Embedding towers into injective split towers

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1 proof footnote
(blueprint: lem-pc-tower-injective-embedding).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

private noncomputable def embeddingTowerObj (J : ℕ → AddCommGrpCat.{u}) :
    ℕ → AddCommGrpCat.{u}
  | 0 => J 0
  | n + 1 => Limits.prod (embeddingTowerObj J n) (J (n + 1))

private noncomputable def embeddingTowerApp (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (J : ℕ → AddCommGrpCat.{u}) (j : ∀ n, A.obj (Opposite.op n) ⟶ J n) :
    ∀ n, A.obj (Opposite.op n) ⟶ embeddingTowerObj J n
  | 0 => j 0
  | n + 1 => Limits.prod.lift
      (A.map (homOfLE (Nat.le_add_right n 1)).op ≫ embeddingTowerApp A J j n) (j (n + 1))

/-- Every inverse system of abelian groups embeds in a tower of injective groups with split
surjective transition maps (Stacks Project, Tag 07KW, Lemma 15.88.1 proof footnote).
The index `n : ℕ` denotes the paper's level `n + 1`.

Proof (node step 1): apply `lem-weil-pbc-ring-modules-enough-injectives` levelwise with
`R = ℤ` to obtain injective groups `J_n` and monomorphisms `j_n : A_n ⟶ J_n`.
Proof (node step 2): set `I_1 = J_1`, `i_1 = j_1`, and recursively `I_{n+1} = I_n ⊕ J_{n+1}`
with the first projection as transition map and `i_{n+1}(a) = (i_n (f_n a), j_{n+1} a)`.
Finite direct sums preserve injectivity, the projections are split by the summand inclusions,
and the defining formula makes the `i_n` a morphism of towers.
Proof (node step 3): each `i_n` is injective by its two coordinates, and a tower morphism with
injective components is a monomorphism of towers since composition is componentwise.
(blueprint: lem-pc-tower-injective-embedding) -/
theorem tower_injective_embedding (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ∃ (I : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (i : A ⟶ I),
      Mono i ∧
        (∀ n : ℕ, Injective (I.obj (Opposite.op n))) ∧
          (∀ n : ℕ,
            IsSplitEpi (I.map (homOfLE (Nat.le_add_right n 1)).op)) := by
  classical
  let J : ℕ → AddCommGrpCat.{u} := fun n ↦ Injective.under (A.obj (Opposite.op n))
  let j : ∀ n, A.obj (Opposite.op n) ⟶ J n := fun n ↦ Injective.ι _
  let p : ∀ n, embeddingTowerObj J (n + 1) ⟶ embeddingTowerObj J n :=
    fun _ ↦ Limits.prod.fst
  let I := Functor.ofOpSequence p
  let i : A ⟶ I := NatTrans.ofOpSequence (embeddingTowerApp A J j) (fun n ↦ by
    dsimp [I, p]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Limits.prod.lift_fst _ _).symm)
  refine ⟨I, i, ?_, ?_, ?_⟩
  · have hm : ∀ n, Mono (embeddingTowerApp A J j n) := by
      intro n
      cases n with
      | zero => exact Injective.ι_mono _
      | succ n =>
        have : Mono (j (n + 1)) := Injective.ι_mono _
        exact mono_of_mono_fac (Limits.prod.lift_snd _ _)
    have : ∀ n, Mono (i.app n) := fun n ↦ hm n.unop
    exact NatTrans.mono_of_mono_app i
  · intro n
    change Injective (embeddingTowerObj J n)
    induction n with
    | zero => exact Injective.injective_under _
    | succ n ih =>
      let := ih
      change Injective (Limits.prod (embeddingTowerObj J n) (J (n + 1)))
      infer_instance
  · intro n
    dsimp [I]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change IsSplitEpi (Limits.prod.fst : Limits.prod (embeddingTowerObj J n) (J (n + 1)) ⟶ _)
    infer_instance

end CategoryTheory
