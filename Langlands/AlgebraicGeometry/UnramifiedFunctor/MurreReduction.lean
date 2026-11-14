import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Murre's criterion from the steps of its proof

`murreCriterion_of_steps` derives `MurreCriterionStatement` from
`MurreProofStepsStatement` by strong induction on the dimension of the local rings. -/

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- The Krull dimension of a local noetherian ring is a natural number. -/
theorem exists_nat_eq_ringKrullDim (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ∃ m : ℕ, ringKrullDim R = m := by
  obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have htop : k ≠ ⊤ := by
    rintro rfl
    exact ringKrullDim_ne_top (R := R) hk.symm
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp htop
  exact ⟨m, by rw [← hk]; rfl⟩

/-- Base change, Proposition 2 and the local step give the criterion over every
locally noetherian base whose local rings have dimension `< n`, for every `n`. -/
theorem murreDimensionBound_of_steps (h0 : MurreBaseChangeStatement.{u, v})
    (h1 : MurreLocalToGlobalStatement.{u, v}) (h2 : MurreLocalStepStatement.{u, v}) :
    ∀ n : ℕ, MurreDimensionBound.{u, v} n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S _ F hF hdim
    refine h1 S F hF fun s ↦ ?_
    obtain ⟨m, hm⟩ := exists_nat_eq_ringKrullDim (S.presheaf.stalk s)
    have hmn : m < n := by
      have h := hdim s
      rw [hm] at h
      exact_mod_cast h
    exact h2 m (ih m hmn) (S.presheaf.stalk s) hm _ (h0 _ _ _ F hF)

/-- Murre's criterion follows from the three steps of its proof. -/
theorem murreCriterion_of_steps (h : MurreProofStepsStatement.{u, v}) :
    MurreCriterionStatement.{u, v} := by
  obtain ⟨h0, h1, h2⟩ := h
  intro S _ F hsmall hzar hflat hcolim hadic hart hnil hval hone hgen
  have hF : MurreConditions F :=
    ⟨hsmall, hzar, hflat, hcolim, hadic, hart, hnil, hval, hone, hgen⟩
  refine h1 S F hF fun s ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_eq_ringKrullDim (S.presheaf.stalk s)
  exact h2 m (murreDimensionBound_of_steps h0 h1 h2 m) (S.presheaf.stalk s) hm _
    (h0 _ _ _ F hF)

end Langlands.AlgebraicGeometry.UnramifiedFunctor
