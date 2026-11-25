/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorSuccessor

/-!
# Effaceable delta-functors are universal

Source: Stacks Project, Homology, Lemma 010T (lemma-efface-implies-universal)
(blueprint: lem-weil-pbc-effaceable-delta-functor-universal).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

private theorem deltaHom_ext
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] {F G : CohomologicalDeltaFunctor A B}
    (φ ψ : CohomologicalDeltaFunctor.Hom F G) (h : φ.app = ψ.app) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- An effaceable cohomological delta-functor is universal.

This is Grothendieck's effacement criterion, Stacks Project, Homology, Lemma 010T.
The proof constructs the extension inductively using the cokernel description supplied
by an effacing short exact sequence; independence of choices, naturality, and
compatibility with connecting morphisms follow from comparison via biproducts and
pushouts, and uniqueness follows by cancellation of the resulting epimorphisms.
(blueprint: lem-weil-pbc-effaceable-delta-functor-universal) -/
theorem effaceable_deltaFunctor_isUniversal
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ (n : ℕ), 0 < n → ∀ (X : A),
      ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F.F n).map u = 0) :
    F.IsUniversal := by
  classical
  intro G t
  let step (n : ℕ) (s : F.F n ⟶ G.F n) : F.F (n + 1) ⟶ G.F (n + 1) :=
    Classical.choose (effaceable_deltaFunctor_successor F hF G n s)
  let ts : ∀ n : ℕ, F.F n ⟶ G.F n := fun n ↦ Nat.rec t step n
  have hts (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact) :
      F.delta S hS n ≫ (ts (n + 1)).app S.X₁ =
        (ts n).app S.X₃ ≫ G.delta S hS n :=
    Classical.choose_spec (effaceable_deltaFunctor_successor F hF G n (ts n)) S hS
  let φ : CohomologicalDeltaFunctor.Hom F G := ⟨ts, fun S hS n ↦ hts n S hS⟩
  refine ⟨φ, rfl, ?_⟩
  intro ψ hψ
  have heq (n : ℕ) : ψ.app n = φ.app n := by
    induction n with
    | zero => exact hψ
    | succ n ih =>
      apply NatTrans.ext
      funext X
      obtain ⟨Y, u, hu, hzero⟩ := hF (n + 1) (Nat.zero_lt_succ n) X
      have : Mono u := hu
      let S := ShortComplex.cokernelSequence u
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact u)
          (show Mono S.f from hu) inferInstance
      obtain ⟨hcomp, hex⟩ := F.exact_left S hS n
      have : Epi (F.delta S hS n) := hex.epi_f hzero
      apply (cancel_epi (F.delta S hS n)).mp
      calc
        F.delta S hS n ≫ (ψ.app (n + 1)).app X =
            (ψ.app n).app S.X₃ ≫ G.delta S hS n := ψ.naturality S hS n
        _ = (φ.app n).app S.X₃ ≫ G.delta S hS n := by rw [ih]
        _ = F.delta S hS n ≫ (φ.app (n + 1)).app X :=
          (φ.naturality S hS n).symm
  exact deltaHom_ext ψ φ (funext heq)

end CategoryTheory
