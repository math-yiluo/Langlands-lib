import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Init
import Lean.Elab.Tactic.Omega

/-! Internal unit-valued algebra for the two descending inductions in JPSS §7.
This draft does not instantiate the algebra on representations or establish any
analytic input. Indices are actual positive ranks minus one. -/

namespace Langlands.RankinSelberg

universe uA uK

section RankDescent

variable {A : ℕ → Type uA} {K : Type uK} [CommGroup K]
  (ind : ∀ {a b}, A a → A b → A (b + 1 + a))
  (gamma : ∀ {r t}, A r → A t → K)
  (mu : A 0)
  (swap : ∀ {r t} (pi : A r) (sigma : A t), gamma pi sigma = gamma sigma pi)

include mu swap

/-- Algebraic cancellation after all five enlargement identities have been
provided. This lemma asserts no factor existence or representation comparison. -/
private theorem cancel_enlargement
    {r a b : ℕ} (pi : A r) (x : A a) (y : A b)
    (hmain : gamma (ind mu pi) (ind x y) =
      gamma (ind mu pi) x * gamma (ind mu pi) y)
    (hsigma : gamma (ind x y) (ind mu pi) =
      gamma (ind x y) mu * gamma (ind x y) pi)
    (hx : gamma x (ind mu pi) = gamma x mu * gamma x pi)
    (hy : gamma y (ind mu pi) = gamma y mu * gamma y pi)
    (hmu : gamma mu (ind x y) = gamma mu x * gamma mu y) :
    gamma pi (ind x y) = gamma pi x * gamma pi y := by
  have hs : gamma (ind mu pi) (ind x y) =
      gamma mu (ind x y) * gamma pi (ind x y) := by
    rw [swap (ind mu pi) (ind x y), hsigma,
      swap (ind x y) mu, swap (ind x y) pi]
  have hxs : gamma (ind mu pi) x = gamma mu x * gamma pi x := by
    rw [swap (ind mu pi) x, hx, swap x mu, swap x pi]
  have hys : gamma (ind mu pi) y = gamma mu y * gamma pi y := by
    rw [swap (ind mu pi) y, hy, swap y mu, swap y pi]
  rw [hs, hxs, hys, hmu] at hmain
  apply mul_left_cancel (a := gamma mu x * gamma mu y)
  calc
    (gamma mu x * gamma mu y) * gamma pi (ind x y) =
        (gamma mu x * gamma pi x) * (gamma mu y * gamma pi y) := hmain
    _ = (gamma mu x * gamma mu y) * (gamma pi x * gamma pi y) :=
      mul_mul_mul_comm _ _ _ _

/-- Conditional two-stage rank descent for symmetric group-valued factors.
The dominant, adjacent and rank-one hypotheses are the three analytic bases.
No associativity or commutativity of the induction operation is assumed. -/
theorem twoBlockGammaRankDescent
    (dominant : ∀ {r a b} (pi : A r) (x : A a) (y : A b), b + 1 + a ≤ r →
      gamma pi (ind x y) = gamma pi x * gamma pi y)
    (adjacent : ∀ {r} (pi : A r) (x : A 0) (y : A r),
      gamma pi (ind x y) = gamma pi x * gamma pi y)
    (rankOne : ∀ {a b} (pi : A 0) (x : A a) (y : A b),
      gamma pi (ind x y) = gamma pi x * gamma pi y) :
    ∀ {r a b} (pi : A r) (x : A a) (y : A b),
      gamma pi (ind x y) = gamma pi x * gamma pi y := by
  have first : ∀ {r b} (pi : A r) (x : A 0) (y : A b),
      gamma pi (ind x y) = gamma pi x * gamma pi y := by
    intro r b
    by_cases h : b + 1 ≤ r
    · intro pi x y
      exact dominant pi x y h
    · have hr : r ≤ b := by omega
      refine Nat.decreasingInduction (motive := fun r _ =>
        ∀ (pi : A r) (x : A 0) (y : A b),
          gamma pi (ind x y) = gamma pi x * gamma pi y) ?_ ?_ hr
      · intro k hk ih pi x y
        exact cancel_enlargement (ind := @ind) (gamma := @gamma) (mu := mu)
          (swap := @swap) pi x y
          (ih (ind mu pi) x y)
          (dominant (ind x y) mu pi (by omega))
          (rankOne x mu pi)
          (dominant y mu pi (by omega))
          (rankOne mu x y)
      · exact adjacent
  intro r a b
  by_cases h : b + 1 + a ≤ r
  · intro pi x y
    exact dominant pi x y h
  · have hr : r ≤ b + 1 + a := by omega
    refine Nat.decreasingInduction (motive := fun r _ =>
      ∀ (pi : A r) (x : A a) (y : A b),
        gamma pi (ind x y) = gamma pi x * gamma pi y) ?_ ?_ hr
    · intro k hk ih pi x y
      exact cancel_enlargement (ind := @ind) (gamma := @gamma) (mu := mu)
        (swap := @swap) pi x y
        (ih (ind mu pi) x y)
        (first (ind x y) mu pi)
        (first x mu pi)
        (first y mu pi)
        (rankOne mu x y)
    · intro pi x y
      exact dominant pi x y (Nat.le_refl _)

end RankDescent

end Langlands.RankinSelberg
