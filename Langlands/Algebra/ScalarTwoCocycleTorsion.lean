import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-! # Finite-group scalar two-cocycle torsion by a product calculation -/

noncomputable section
universe u v
open scoped BigOperators

namespace Langlands.ScalarTwoCocycle

variable {Γ : Type u} [Group Γ] {A : Type v} [CommGroup A] [MulDistribMulAction Γ A]

/-- The inhomogeneous multiplicative two-cocycle identity. -/
def IsTwoCocycle (c : Γ → Γ → A) : Prop :=
  ∀ g h t, c g h * c (g * h) t = (g • c h t) * c g (h * t)

/-- The multiplicative two-coboundary of a one-cochain. -/
def coboundary (b : Γ → A) (g h : Γ) : A :=
  b g * (g • b h) * (b (g * h))⁻¹

/-- An actual one-cochain trivializes the given scalar two-cochain. -/
def IsCoboundary (c : Γ → Γ → A) : Prop :=
  ∃ b : Γ → A, ∀ g h, c g h = coboundary b g h

/-- Multiplication of one-cochains multiplies their coboundaries. -/
theorem coboundary_mul (b d : Γ → A) (g h : Γ) :
    coboundary (fun t => b t * d t) g h = coboundary b g h * coboundary d g h := by
  simp only [coboundary, smul_mul', mul_inv_rev]
  ac_rfl

/-- Integer powers of one-cochains induce the same powers of their coboundaries. -/
theorem coboundary_zpow (b : Γ → A) (a : ℤ) (g h : Γ) :
    coboundary (fun t => b t ^ a) g h = coboundary b g h ^ a := by
  simp only [coboundary, smul_zpow', mul_zpow, inv_zpow]

/-- The product of a cocycle along its second variable is an explicit cochain. -/
def productCochain [Fintype Γ] (c : Γ → Γ → A) (g : Γ) : A := ∏ t, c g t

/-- The group order power of a scalar two-cocycle is an explicit coboundary. -/
theorem card_power_eq_coboundary [Fintype Γ] {c : Γ → Γ → A} (hc : IsTwoCocycle c)
    (g h : Γ) :
    c g h ^ Fintype.card Γ = coboundary (productCochain c) g h := by
  classical
  have hp : (∏ t, c g (h * t)) = ∏ t, c g t :=
    Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
  have he := congrArg (fun f : Γ → A => ∏ t, f t) (funext (hc g h))
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at he
  rw [← Finset.smul_prod', hp] at he
  apply (eq_mul_inv_iff_mul_eq).mpr
  exact he.trans (mul_comm _ _)

/-- Every scalar two-cocycle on a finite group is killed by the group order. -/
theorem card_power_isCoboundary [Fintype Γ] {c : Γ → Γ → A} (hc : IsTwoCocycle c) :
    IsCoboundary (fun g h => c g h ^ Fintype.card Γ) :=
  ⟨productCochain c, card_power_eq_coboundary hc⟩

/-- If two coprime powers are actual coboundaries, so is the scalar cochain itself. -/
theorem isCoboundary_of_coprime_powers {c : Γ → Γ → A} {m n : ℕ}
    (hmn : m.Coprime n) (hm : IsCoboundary (fun g h => c g h ^ m))
    (hn : IsCoboundary (fun g h => c g h ^ n)) : IsCoboundary c := by
  obtain ⟨b, hb⟩ := hm
  obtain ⟨d, hd⟩ := hn
  refine ⟨fun t => b t ^ Nat.gcdA m n * d t ^ Nat.gcdB m n, fun g h => ?_⟩
  have he : (1 : ℤ) = (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n := by
    simpa only [hmn.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab m n)
  rw [coboundary_mul, coboundary_zpow, coboundary_zpow, ← hb, ← hd]
  calc
    c g h = c g h ^ (1 : ℤ) := (zpow_one _).symm
    _ = _ := by rw [he, zpow_add, zpow_mul, zpow_mul]; simp only [zpow_natCast]

/-- A power prime to the group order can be a coboundary only for a trivial class. -/
theorem isCoboundary_of_coprime_card [Fintype Γ] {c : Γ → Γ → A}
    (hc : IsTwoCocycle c) {m : ℕ} (hm : m.Coprime (Fintype.card Γ))
    (hpow : IsCoboundary (fun g h => c g h ^ m)) : IsCoboundary c :=
  isCoboundary_of_coprime_powers hm hpow (card_power_isCoboundary hc)

end Langlands.ScalarTwoCocycle
