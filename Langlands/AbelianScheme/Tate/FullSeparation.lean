import Langlands.AbelianScheme.Tate.PrimeAdic
import Langlands.AbelianScheme.Tate.Rational
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Factorial.Basic

/-! # Separation and coordinate surjectivity for full integral Tate groups -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

lemma toSection_transition {n m : ℕ} (h : n ∣ m) (x : Level G T m) :
    toSection G T n (transition G T h x) =
      (m / n) • toSection G T m x := rfl

/-- Every positive integer acts injectively on the full inverse limit. -/
theorem full_eq_zero_of_nsmul_eq_zero {k : ℕ} (hk : 0 < k) {x : Full G T}
    (h : k • x = 0) : x = 0 := by
  apply Subtype.ext
  funext n
  let m : Index (fun _ => True) := ⟨n.val * k, Nat.mul_pos n.property.1 hk, trivial⟩
  have hx := congrArg (evaluation G T (fun _ => True) m) h
  rw [map_nsmul, map_zero] at hx
  apply toSection_injective G T n.val
  change toSection G T n.val (evaluation G T (fun _ => True) n x) =
    toSection G T n.val 0
  rw [← evaluation_transition G T (fun _ => True) n m (dvd_mul_right _ _) x,
    toSection_transition]
  change (n.val * k / n.val) • toSection G T m.val
    (evaluation G T (fun _ => True) m x) = _
  rw [Nat.mul_div_cancel_left _ n.property.1, ← map_nsmul, hx, map_zero, map_zero]

theorem full_eq_zero_of_zsmul_eq_zero {k : ℤ} (hk : k ≠ 0) {x : Full G T}
    (h : k • x = 0) : x = 0 := by
  apply full_eq_zero_of_nsmul_eq_zero G T (Int.natAbs_pos.mpr hk)
  exact (natAbs_nsmul_eq_zero).mpr h

/-- The full integral Tate group embeds in its rationalization. -/
theorem full_toRational_injective :
    Function.Injective (toRational G T (fun _ => True)) := by
  let : IsLocalizedModule (nonZeroDivisors ℤ)
      (toRational G T (fun _ => True)) :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
  intro x y hxy
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) hxy
  rw [← sub_eq_zero]
  apply full_eq_zero_of_zsmul_eq_zero G T (nonZeroDivisors.coe_ne_zero c)
  rw [smul_sub, sub_eq_zero]
  simpa only [Submonoid.smul_def] using hc

/-- Divisibility of sections makes every transition between positive levels surjective. -/
theorem full_transition_surjective_of_pow
    (hdiv : ∀ k : ℕ, 0 < k → ∀ y : T ⟶ G.X, ∃ x, x ^ k = y)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : n ∣ m) :
    Function.Surjective (transition G T h) := by
  intro y
  have hquot : 0 < m / n := Nat.div_pos (Nat.le_of_dvd hm h) hn
  obtain ⟨x, hx⟩ := hdiv (m / n) hquot (Additive.toMul y).val
  have hmem : x ∈ levelGroup G T m := by
    rw [mem_levelGroup, ← Nat.div_mul_cancel h, pow_mul, hx]
    exact (mem_levelGroup G T n _).mp (Additive.toMul y).property
  refine ⟨Additive.ofMul ⟨x, hmem⟩, ?_⟩
  apply toSection_injective G T n
  exact hx

/-- A factorial cofinal tower extends any positive-level point to a full coherent family. -/
theorem full_evaluation_surjective
    (hsurj : ∀ (n m : ℕ) (_hn : 0 < n) (_hm : 0 < m) (h : n ∣ m),
      Function.Surjective (transition G T h))
    (n : Index (fun _ => True)) :
    Function.Surjective (evaluation G T (fun _ => True) n) := by
  intro y
  let N : ℕ → ℕ | 0 => n.val | k + 1 => n.val * (k + 1).factorial
  have hNeq : ∀ k, N k = n.val * k.factorial := by
    intro k
    cases k <;> simp [N]
  have hN : ∀ k, 0 < N k := by
    intro k
    rw [hNeq]
    exact Nat.mul_pos n.property.1 (Nat.factorial_pos k)
  have hdvd : ∀ {i j : ℕ}, i ≤ j → N i ∣ N j := by
    intro i j h
    rw [hNeq, hNeq]
    exact Nat.mul_dvd_mul_left n.val (Nat.factorial_dvd_factorial h)
  let w : (k : ℕ) → Level G T (N k) := fun k =>
    Nat.rec (motive := fun k => Level G T (N k)) y
      (fun k z => Classical.choose (hsurj (N k) (N (k + 1)) (hN k) (hN (k + 1))
        (hdvd (Nat.le_succ k)) z)) k
  have hw : ∀ k, transition G T (hdvd (Nat.le_succ k)) (w (k + 1)) = w k :=
    fun k => Classical.choose_spec
      (hsurj (N k) (N (k + 1)) (hN k) (hN (k + 1)) (hdvd (Nat.le_succ k)) (w k))
  have hwcomp : ∀ (i j : ℕ) (h : i ≤ j), transition G T (hdvd h) (w j) = w i := by
    intro i j h
    induction j, h using Nat.le_induction with
    | base => exact transition_self G T (hN i) (w i)
    | succ j hij ih =>
      rw [← hw j, transition_comp] at ih
      exact ih
  have hi : ∀ (i : Index (fun _ => True)) (k : ℕ), i.val ≤ k → i.val ∣ N k := by
    intro i k hik
    rw [hNeq]
    exact dvd_mul_of_dvd_right (Nat.dvd_factorial i.property.1 hik) n.val
  let x : Full G T := ⟨fun i => transition G T (hi i i.val le_rfl) (w i.val), by
    intro i j hij
    let k := max i.val j.val
    have hik : i.val ≤ k := le_max_left _ _
    have hjk : j.val ≤ k := le_max_right _ _
    change transition G T hij (transition G T _ (w j.val)) =
      transition G T _ (w i.val)
    rw [← hwcomp j.val k hjk, ← hwcomp i.val k hik,
      transition_comp, transition_comp, transition_comp]⟩
  refine ⟨x, ?_⟩
  have h0 := hwcomp 0 n.val (Nat.zero_le _)
  change transition G T (hi n n.val le_rfl) (w n.val) = y
  exact h0

theorem full_evaluation_surjective_of_pow
    (hdiv : ∀ k : ℕ, 0 < k → ∀ y : T ⟶ G.X, ∃ x, x ^ k = y)
    (n : Index (fun _ => True)) :
    Function.Surjective (evaluation G T (fun _ => True) n) :=
  full_evaluation_surjective G T
    (fun _ _ hn hm h => full_transition_surjective_of_pow G T hdiv hn hm h) n

end Langlands.GroupScheme.Tate
