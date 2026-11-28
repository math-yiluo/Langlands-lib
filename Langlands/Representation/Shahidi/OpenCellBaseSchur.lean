import Langlands.Representation.Shahidi.OpenCellBaseInduction
import Langlands.Representation.RankinSelberg.SymmetricDominant
import Langlands.Representation.RankinSelberg.UnramifiedRecursionUniqueness
import Langlands.Representation.Conductor.SphericalDualParameters

/-! # The Schur function at `(0, …, 0, -1, …, -1)`

For a natural number `d ≤ t + 1` and the weight `κ(t, d) = (0, …, 0, -1, …, -1)` with `d` entries
`-1`, the Schur function is the elementary symmetric function of the inverse parameters:
`s_κ(c) = e_d(c⁻¹)`.
(For `d > t + 1` the weight is `(-1, …, -1)` and the identity fails, e.g. `t = 0`, `d = 2`,
`c = 1`.) -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell.Base

open Langlands.GeneralLinear Langlands.GeneralLinear.Spherical MvPolynomial

theorem antitone_baseKappa (t D : ℕ) : Antitone (baseKappa t D) := by
  intro i j hij
  simp only [baseKappa]
  have hij' : (i : ℕ) ≤ j := hij
  split_ifs with h1 h2 h2 <;> omega

/-- The indicator of the first `d` coordinates. -/
def initialIndicator (t D : ℕ) : Fin (t + 1) → ℤ := fun i => if (i : ℕ) < D then 1 else 0

theorem dualWeight_baseKappa (t D : ℕ) :
    Conductor.dualWeight (baseKappa t D) = initialIndicator t D := by
  funext i
  simp only [Conductor.dualWeight, baseKappa, initialIndicator, Fin.val_rev]
  have := i.isLt
  split_ifs with h1 h2 h2 <;> omega

theorem antitone_initialIndicator (t D : ℕ) : Antitone (initialIndicator t D) := by
  intro i j hij
  simp only [initialIndicator]
  have hij' : (i : ℕ) ≤ j := hij
  split_ifs with h1 h2 h2 <;> omega

theorem initialIndicator_nonneg (t D : ℕ) (i : Fin (t + 1)) : 0 ≤ initialIndicator t D i := by
  simp only [initialIndicator]
  split_ifs <;> omega

theorem raiseWeight_zero_initialSegment (t D : ℕ) :
    raiseWeight (0 : Fin (t + 1) → ℤ) (RankinSelberg.UnramifiedWhittaker.initialSegment (t + 1) D) =
      initialIndicator t D := by
  funext i
  simp only [raiseWeight, Pi.zero_apply, zero_add, initialIndicator,
    RankinSelberg.UnramifiedWhittaker.mem_initialSegment]

/-- **The column Jacobi–Trudi determinant is the elementary symmetric polynomial.** -/
theorem jacobiTrudi_initialIndicator (t D : ℕ) (hD : D ≤ t + 1) :
    jacobiTrudi ℂ (initialIndicator t D) = esymm (Fin (t + 1)) ℂ D := by
  have h0 : Antitone (0 : Fin (t + 1) → ℤ) := fun _ _ _ => le_rfl
  have h := dominantJacobiTrudi_mul_esymm (R := ℂ) (0 : Fin (t + 1) → ℤ) h0 (fun _ => le_rfl) D
  rw [dominantJacobiTrudi, ite_eq_left h0, jacobiTrudi_zero, one_mul] at h
  rw [h, Finset.sum_eq_single (RankinSelberg.UnramifiedWhittaker.initialSegment (t + 1) D)]
  · rw [raiseWeight_zero_initialSegment, dominantJacobiTrudi,
      ite_eq_left (antitone_initialIndicator t D)]
  · intro s hs hne
    rw [Finset.mem_powersetCard] at hs
    rw [dominantJacobiTrudi, ite_eq_right]
    intro hanti
    apply hne
    have hdown : ∀ i j, i ≤ j → j ∈ s → i ∈ s := by
      intro i j hij hj
      have := hanti hij
      simp only [raiseWeight, Pi.zero_apply, zero_add, hj, ite_true] at this
      by_contra hi
      rw [ite_eq_right hi] at this
      omega
    rw [RankinSelberg.UnramifiedWhittaker.eq_initialSegment_of_downward hdown, hs.2]
  · intro hn
    exfalso
    apply hn
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    exact RankinSelberg.UnramifiedWhittaker.card_initialSegment hD

/-- **`s_κ(c) = e_D(c⁻¹)` for `D ≤ t + 1`.** -/
theorem satakeSchur_baseKappa {t : ℕ} (c : Fin (t + 1) → ℂˣ) {D : ℕ} (hD : D ≤ t + 1) :
    satakeSchur c (baseKappa t D) =
      ∑ S ∈ Finset.powersetCard D (Finset.univ : Finset (Fin (t + 1))),
        ∏ j ∈ S, ((c j : ℂ))⁻¹ := by
  have h := Conductor.satakeSchur_inv (c⁻¹) (antitone_baseKappa t D)
  rw [inv_inv] at h
  rw [h, dualWeight_baseKappa,
    satakeSchur_eq_eval_jacobiTrudi _ _ (antitone_initialIndicator t D)
      (initialIndicator_nonneg t D), jacobiTrudi_initialIndicator t D hD]
  simp only [esymm, map_sum, map_prod, eval_X, Pi.inv_apply, Units.val_inv_eq_inv_val]

end Langlands.Shahidi.OpenCell.Base
