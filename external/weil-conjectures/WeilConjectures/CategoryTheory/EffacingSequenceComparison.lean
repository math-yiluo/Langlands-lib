/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DeltaFunctor

/-!
# Comparing effacing short exact sequences

Source: Stacks Project, Homology, Lemma 010T and the parent node's comparison arguments.
(blueprint: lem-weil-pbc-effacing-sequence-comparison).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

/-- Comparison span for effacing sequences.

Source: Stacks Project, Homology, Lemma 010T, omitted naturality verification;
the direct-sum argument is step 5 of the parent node. Form the embedding
w = (S.f, a ≫ T.f) into the biproduct. Projection onto the first factor proves
monicity. Additivity and the two effacement equations show F(w) = 0. The
projections followed by the quotient maps kill w, so they descend through its
cokernel and define the two morphisms of short exact sequences.
(blueprint: lem-weil-pbc-effacing-sequence-comparison) -/
theorem effacingSequence_comparison
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] (F : CohomologicalDeltaFunctor A B) (n : ℕ)
    (S T : ShortComplex A) (hS : S.ShortExact) (_hT : T.ShortExact)
    (hs : (F.F (n + 1)).map S.f = 0) (ht : (F.F (n + 1)).map T.f = 0)
    (a : S.X₁ ⟶ T.X₁) :
    ∃ (Y : A) (u : S.X₁ ⟶ Y), Mono u ∧ (F.F (n + 1)).map u = 0 ∧
      ∃ (p : ShortComplex.cokernelSequence u ⟶ S)
        (q : ShortComplex.cokernelSequence u ⟶ T), p.τ₁ = 𝟙 S.X₁ ∧ q.τ₁ = a := by
  have := hS.mono_f
  have := (F.additive (n + 1))
  let w := biprod.lift S.f (a ≫ T.f)
  have hw : Mono w := by
    apply mono_of_mono_fac (show w ≫ biprod.fst = S.f from biprod.lift_fst _ _)
  have hz : (F.F (n + 1)).map w = 0 := by
    dsimp [w]
    rw [biprod.lift_eq, Functor.map_add, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, hs, ht]
    simp
  have hpzero : w ≫ (biprod.fst ≫ S.g) = 0 := by
    rw [← Category.assoc, biprod.lift_fst, S.zero]
  have hqzero : w ≫ (biprod.snd ≫ T.g) = 0 := by
    rw [← Category.assoc, biprod.lift_snd, Category.assoc, T.zero, comp_zero]
  let p : ShortComplex.cokernelSequence w ⟶ S :=
    { τ₁ := 𝟙 S.X₁
      τ₂ := biprod.fst
      τ₃ := cokernel.desc w (biprod.fst ≫ S.g) hpzero
      comm₁₂ := by
        change 𝟙 S.X₁ ≫ S.f = w ≫ biprod.fst
        rw [id_comp, biprod.lift_fst]
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  let q : ShortComplex.cokernelSequence w ⟶ T :=
    { τ₁ := a
      τ₂ := biprod.snd
      τ₃ := cokernel.desc w (biprod.snd ≫ T.g) hqzero
      comm₁₂ := (biprod.lift_snd _ _).symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  exact ⟨_, w, hw, hz, p, q, rfl, rfl⟩

end CategoryTheory
