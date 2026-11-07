import Langlands.Weil.Representation.CoinductionDegreeCoordinates

/-!
# Cyclic Frobenius in degree coordinates

Transport of the actual coinduced invariant action has the cyclic-block formulas.
-/

noncomputable section

namespace Langlands.FiniteRepresentation.InductionDegree

universe uK uG uH uV

variable {K : Type uK} [Field K]
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable (dG : G →* Multiplicative ℤ) (dH : H →* Multiplicative ℤ)
variable (ι : H →* G) (ρ : Representation K H V)
variable (n : ℕ)
variable (hdeg : ∀ h : H,
  intDegree dG (ι h) = ((n + 1 : ℕ) : ℤ) * intDegree dH h)
variable (Φ : G) (hΦ : intDegree dG Φ = 1)
variable (η : H) (hη : intDegree dH η = 1)

include hdeg hΦ hη in
theorem coordinates_action_zero (u : Target dG ι ρ) :
    coordinates dG dH ι ρ (n + 1) (Nat.succ_pos n) hdeg Φ hΦ η hη
        (((Representation.coind ι ρ).toInvariants dG.ker) Φ u) 0 =
      ((ρ.toInvariants dH.ker) η)
        (coordinates dG dH ι ρ (n + 1) (Nat.succ_pos n) hdeg Φ hΦ η hη
          u (Fin.last n)) := by
  apply Subtype.ext
  change u.val.val (Φ ^ (-(0 : ℤ)) * Φ) =
    ρ η (u.val.val (Φ ^ (-(n : ℤ))))
  simp only [neg_zero, zpow_zero, one_mul]
  rw [← u.val.property]
  apply target_value_eq_of_degree_eq
  simp only [intDegree_mul, hdeg, intDegree_zpow, hΦ, hη, mul_one]
  push_cast
  ring

include hΦ in
theorem coordinates_action_succ (u : Target dG ι ρ) (i : Fin n) :
    coordinates dG dH ι ρ (n + 1) (Nat.succ_pos n) hdeg Φ hΦ η hη
        (((Representation.coind ι ρ).toInvariants dG.ker) Φ u) i.succ =
      coordinates dG dH ι ρ (n + 1) (Nat.succ_pos n) hdeg Φ hΦ η hη
        u i.castSucc := by
  apply Subtype.ext
  change u.val.val (Φ ^ (-((i.succ : Fin (n + 1)) : ℤ)) * Φ) =
    u.val.val (Φ ^ (-((i.castSucc : Fin (n + 1)) : ℤ)))
  apply target_value_eq_of_degree_eq
  simp only [intDegree_mul, intDegree_zpow, hΦ, mul_one, Fin.val_succ,
    Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- The ambient degree-one action transported through degree coordinates. -/
def cyclicOperator : Module.End K (Fin (n + 1) → Source dH ρ) :=
  (coordinates dG dH ι ρ (n + 1) (Nat.succ_pos n) hdeg Φ hΦ η hη).conj
    (((Representation.coind ι ρ).toInvariants dG.ker) Φ)

theorem cyclicOperator_zero (v : Fin (n + 1) → Source dH ρ) :
    cyclicOperator dG dH ι ρ n hdeg Φ hΦ η hη v 0 =
      ((ρ.toInvariants dH.ker) η) (v (Fin.last n)) := by
  simp only [cyclicOperator, LinearEquiv.conj_apply_apply]
  rw [coordinates_action_zero dG dH ι ρ n hdeg Φ hΦ η hη,
    LinearEquiv.apply_symm_apply]

theorem cyclicOperator_succ (v : Fin (n + 1) → Source dH ρ) (i : Fin n) :
    cyclicOperator dG dH ι ρ n hdeg Φ hΦ η hη v i.succ = v i.castSucc := by
  simp only [cyclicOperator, LinearEquiv.conj_apply_apply]
  rw [coordinates_action_succ dG dH ι ρ n hdeg Φ hΦ η hη,
    LinearEquiv.apply_symm_apply]

end Langlands.FiniteRepresentation.InductionDegree
