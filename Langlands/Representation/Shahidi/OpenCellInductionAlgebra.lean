import Langlands.Representation.Shahidi.OpenCellInductionSeries

/-! # The algebra of the induction step

Scaling the variables of `∏_p (1 - x_p)` multiplies its degree-`D` coefficient by the `D`-th
power of the scalar, so the coefficients sum to `∏_p (1 - w x_p)` against `w^D`. The rank-one
coefficients for the parameters `a₁` and `(Z a', c)`, weighted by `(X Z)^(e₁)` and multiplied by
`∏_(j,l) (1 - Z a'_j c_l⁻¹ q⁻¹)`, sum to
`∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) · ∏_(i,l) (1 - Z (X a₁, a')_i c_l⁻¹ q⁻¹)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

section Coefficients

theorem shellCoefficient_smul {ι : Type*} [Fintype ι] (w : ℂ) (v : ι → ℂ) (D : ℕ) :
    shellCoefficient (fun i => w * v i) D = w ^ D * shellCoefficient v D := by
  unfold shellCoefficient
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_powersetCard] at hT
  have h : ∀ i, -(w * v i) = w * (-v i) := fun i => by ring
  simp_rw [h, Finset.prod_mul_distrib, Finset.prod_const, hT.2]

theorem shellCoefficient_eq_zero {ι : Type*} [Fintype ι] (v : ι → ℂ) {D : ℕ}
    (hD : Fintype.card ι < D) : shellCoefficient v D = 0 := by
  unfold shellCoefficient
  rw [Finset.powersetCard_eq_empty.2 (by simpa using hD), Finset.sum_empty]

theorem sum_range_pow_mul_shellCoefficient {ι : Type*} [Fintype ι] (w : ℂ) (v : ι → ℂ) {N : ℕ}
    (hN : Fintype.card ι < N) :
    ∑ e ∈ Finset.range N, w ^ e * shellCoefficient v e = ∏ i, (1 - w * v i) := by
  have h := hasSum_shellCoefficient (fun i => w * v i)
  have h2 : HasSum (fun e => shellCoefficient (fun i => w * v i) e)
      (∑ e ∈ Finset.range N, shellCoefficient (fun i => w * v i) e) :=
    hasSum_sum_of_ne_finset_zero fun e he => by
      rw [Finset.mem_range, not_lt] at he
      exact shellCoefficient_eq_zero _ (by omega)
  rw [h.unique h2]
  exact Finset.sum_congr rfl fun e _ => (shellCoefficient_smul w v e).symm

theorem hasSum_pow_mul_shellCoefficient {ι : Type*} [Fintype ι] (w : ℂ) (v : ι → ℂ) :
    HasSum (fun e => shellCoefficient v e * w ^ e) (∏ i, (1 - w * v i)) := by
  have h := hasSum_shellCoefficient (fun i => w * v i)
  convert h using 1
  funext e
  rw [shellCoefficient_smul, mul_comm]

end Coefficients

section Identity

variable (q : ℕ) {d t : ℕ} (a₁ : Fin (0 + 1) → ℂˣ) (a' : Fin (d + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ)

/-- **The product identity of the induction step.** -/
theorem sum_threeBlock_identity (X Z : ℂˣ) :
    ∑ e ∈ Finset.range (d + 1 + t + 1 + 1), (X : ℂ) ^ e *
      ((Z : ℂ) ^ e * (∏ x, (1 - (Z : ℂ) * pairParameter q a' c 0 x)) *
        shellCoefficient (pairParameter q a₁
          (Fin.append (m := d + 1) (n := t + 1) (fun j => Z * a' j) c) 0) e) =
      (∏ x, (1 - (X : ℂ) * pairParameter q a₁ a' 0 x)) *
        ∏ x, (1 - (Z : ℂ) * pairParameter (r := 0 + 1 + d) (t := t) q
          (Fin.append (m := 0 + 1) (n := d + 1) (fun i => X * a₁ i) a') c 0 x) := by
  have hcard : Fintype.card (Fin (0 + 1) × Fin ((d + 1) + (t + 1))) < d + 1 + t + 1 + 1 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hsum : ∑ e ∈ Finset.range (d + 1 + t + 1 + 1), (X : ℂ) ^ e *
      ((Z : ℂ) ^ e * (∏ x, (1 - (Z : ℂ) * pairParameter q a' c 0 x)) *
        shellCoefficient (pairParameter q a₁
          (Fin.append (m := d + 1) (n := t + 1) (fun j => Z * a' j) c) 0) e) =
      (∏ x, (1 - (Z : ℂ) * pairParameter q a' c 0 x)) *
        ∑ e ∈ Finset.range (d + 1 + t + 1 + 1), ((X : ℂ) * Z) ^ e *
          shellCoefficient (pairParameter q a₁
            (Fin.append (m := d + 1) (n := t + 1) (fun j => Z * a' j) c) 0) e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_pow]
    ring
  rw [hsum, sum_range_pow_mul_shellCoefficient _ _ hcard]
  have hZ : (Z : ℂ) ≠ 0 := Z.ne_zero
  have hone : ∀ f : Fin (0 + 1) → ℂ, ∏ i, f i = f 0 := fun f => by
    rw [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  have hsplit₁ : ∀ f : Fin ((d + 1) + (t + 1)) → ℂ,
      ∏ i, f i = (∏ j : Fin (d + 1), f (j.castAdd (t + 1))) * ∏ l : Fin (t + 1), f (l.natAdd (d + 1)) :=
    fun f => Fin.prod_univ_add f
  have hsplit₂ : ∀ f : Fin (0 + 1 + d + 1) → ℂ,
      ∏ i, f i = (∏ j : Fin (0 + 1), f (j.castAdd (d + 1))) * ∏ l : Fin (d + 1), f (l.natAdd (0 + 1)) :=
    fun f => Fin.prod_univ_add (a := 0 + 1) (b := d + 1) f
  simp only [Fintype.prod_prod_type]
  simp only [hsplit₁, hsplit₂]
  simp only [hone, Fin.append_left, Fin.append_right, pairParameter, Units.val_mul]
  have h1 : ∏ j : Fin (d + 1), (1 - (X : ℂ) * Z *
      ((a₁ 0 : ℂ) * ((Z : ℂ) * (a' j : ℂ))⁻¹ * (q : ℂ) ^ (-(1 + (0 : ℂ))))) =
      ∏ j : Fin (d + 1), (1 - (X : ℂ) *
        ((a₁ 0 : ℂ) * ((a' j : ℂ))⁻¹ * (q : ℂ) ^ (-(1 + (0 : ℂ))))) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp
  have h2 : ∏ l : Fin (t + 1), (1 - (X : ℂ) * Z *
      ((a₁ 0 : ℂ) * ((c l : ℂ))⁻¹ * (q : ℂ) ^ (-(1 + (0 : ℂ))))) =
      ∏ l : Fin (t + 1), (1 - (Z : ℂ) *
        ((X : ℂ) * (a₁ 0 : ℂ) * ((c l : ℂ))⁻¹ * (q : ℂ) ^ (-(1 + (0 : ℂ))))) := by
    refine Finset.prod_congr rfl fun l _ => ?_
    ring
  rw [h1, h2]
  ring

end Identity

end Langlands.Shahidi.OpenCell
