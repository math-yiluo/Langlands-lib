import Langlands.GroupScheme.Examples.SU3RootOppositeCommutator

/-! # Explicit big-cell factors for opposite quadratic root parameters -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u

variable {L : Type u} [Field L] {c : RingInvolution L}

/-- The leading entry in the product of an upper and an opposite root matrix. -/
def oppositeProductPivot (p q : Parameters c) : L :=
  1 - p.first * c.bar q.first + p.second * q.second

theorem bar_oppositeProductPivot (p q : Parameters c) :
    c.bar (oppositeProductPivot p q) =
      1 - c.bar p.first * q.first + c.bar p.second * c.bar q.second := by
  simp [oppositeProductPivot]

/-- The upper coordinate in the big-cell decomposition of an upper/opposite product. -/
def oppositeProductUpper (p q : Parameters c) (h : oppositeProductPivot p q ≠ 0) :
    Parameters c :=
  ⟨((p.first - p.second * q.first) / oppositeProductPivot p q,
      p.second / oppositeProductPivot p q), by
    change p.second / oppositeProductPivot p q +
      c.bar (p.second / oppositeProductPivot p q) =
        ((p.first - p.second * q.first) / oppositeProductPivot p q) *
          c.bar ((p.first - p.second * q.first) / oppositeProductPivot p q)
    have hb : c.bar (oppositeProductPivot p q) ≠ 0 := by simpa using h
    simp only [map_div₀, map_sub, map_mul]
    field_simp
    rw [bar_oppositeProductPivot]
    unfold oppositeProductPivot
    linear_combination p.equation + p.second * c.bar p.second * q.equation⟩

@[simp] theorem oppositeProductUpper_first (p q : Parameters c)
    (h : oppositeProductPivot p q ≠ 0) :
    (oppositeProductUpper p q h).first =
      (p.first - p.second * q.first) / oppositeProductPivot p q := rfl

@[simp] theorem oppositeProductUpper_second (p q : Parameters c)
    (h : oppositeProductPivot p q ≠ 0) :
    (oppositeProductUpper p q h).second = p.second / oppositeProductPivot p q := rfl

/-- The opposite coordinate in the big-cell decomposition of an upper/opposite product. -/
def oppositeProductLower (p q : Parameters c) (h : oppositeProductPivot p q ≠ 0) :
    Parameters c :=
  ⟨((q.first - p.first * c.bar q.second) / c.bar (oppositeProductPivot p q),
      q.second / oppositeProductPivot p q), by
    change q.second / oppositeProductPivot p q +
      c.bar (q.second / oppositeProductPivot p q) =
        ((q.first - p.first * c.bar q.second) / c.bar (oppositeProductPivot p q)) *
          c.bar ((q.first - p.first * c.bar q.second) / c.bar (oppositeProductPivot p q))
    have hb : c.bar (oppositeProductPivot p q) ≠ 0 := by simpa using h
    simp only [map_div₀, map_sub, map_mul, RingInvolution.bar_bar]
    field_simp
    rw [bar_oppositeProductPivot]
    unfold oppositeProductPivot
    linear_combination q.equation + q.second * c.bar q.second * p.equation⟩

@[simp] theorem oppositeProductLower_first (p q : Parameters c)
    (h : oppositeProductPivot p q ≠ 0) :
    (oppositeProductLower p q h).first =
      (q.first - p.first * c.bar q.second) / c.bar (oppositeProductPivot p q) := rfl

@[simp] theorem oppositeProductLower_second (p q : Parameters c)
    (h : oppositeProductPivot p q ≠ 0) :
    (oppositeProductLower p q h).second = q.second / oppositeProductPivot p q := rfl

/-- A nonzero leading pivot gives an actual opposite/diagonal/upper factorization. -/
theorem upper_mul_opposite_factorization (p q : Parameters c)
    (h : oppositeProductPivot p q ≠ 0) :
    Parameters.embedding c p * oppositeEmbedding c q =
      oppositeEmbedding c (oppositeProductLower p q h) *
        diagonal c (Units.mk0 (oppositeProductPivot p q) h) *
          Parameters.embedding c (oppositeProductUpper p q h) := by
  have hb : c.bar (oppositeProductPivot p q) ≠ 0 := by simpa using h
  apply Units.ext
  change Parameters.matrix p * (oppositeEmbedding c q : Matrix (Fin 3) (Fin 3) L) =
    (oppositeEmbedding c (oppositeProductLower p q h) : Matrix (Fin 3) (Fin 3) L) *
      (diagonal c (Units.mk0 (oppositeProductPivot p q) h) :
        Matrix (Fin 3) (Fin 3) L) *
      Parameters.matrix (oppositeProductUpper p q h)
  rw [oppositeEmbedding_val, oppositeEmbedding_val, diagonal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Parameters.matrix,
      barUnit, Matrix.mul_apply, Fin.sum_univ_three,
      map_div₀, map_sub, map_mul, RingInvolution.bar_bar, Units.val_inv_eq_inv_val] <;>
    field_simp <;>
    (try rw [bar_oppositeProductPivot]) <;>
    (try unfold oppositeProductPivot) <;>
    first
    | (solve | ring)
    | linear_combination c.bar q.first * p.equation
    | linear_combination -p.first * q.equation
    | linear_combination -c.bar q.second * p.equation +
        (p.second - p.first * c.bar p.first) * q.equation
    | linear_combination -q.second * p.equation +
        (c.bar p.second - p.first * c.bar p.first) * q.equation

/-- Explicit factors for the KP opposite-root commutator, with no lifting assumption. -/
theorem oppositeCommutator_factorization (p q : Parameters c)
    (h : oppositeProductPivot p q ≠ 0) :
    oppositeCommutator p q =
      oppositeEmbedding c (q⁻¹ * oppositeProductLower p q h) *
        diagonal c (Units.mk0 (oppositeProductPivot p q) h) *
          Parameters.embedding c (oppositeProductUpper p q h * p⁻¹) := by
  calc
    oppositeCommutator p q =
      (oppositeEmbedding c q)⁻¹ *
        (Parameters.embedding c p * oppositeEmbedding c q) *
          (Parameters.embedding c p)⁻¹ := by
            simp only [oppositeCommutator, mul_assoc]
    _ = _ := by
      rw [upper_mul_opposite_factorization p q h]
      simp only [map_mul, map_inv, mul_assoc]

/-- For a doubled input, the pivot differs from one by the product of the second coordinates. -/
theorem oppositeProductPivot_sub_one_of_double (p q : Parameters c)
    (hdouble : p.first = 0 ∨ q.first = 0) :
    oppositeProductPivot p q - 1 = p.second * q.second := by
  rcases hdouble with hp | hq
  · simp [oppositeProductPivot, hp]
  · simp [oppositeProductPivot, hq]

section Valuation

variable (omega : AddValuation L (WithTop ℝ))

/-- The ordinary pivot deviation has at least the sum of two lower depth bounds. -/
theorem value_oppositeProductPivot_sub_one_ge
    (hinv : ∀ z : L, omega (c.bar z) = omega z)
    (p q : Parameters c) (r s : ℝ) (hrs : 0 ≤ r + s)
    (hp : (r : WithTop ℝ) ≤ Parameters.depthA omega p)
    (hq : (s : WithTop ℝ) ≤ Parameters.depthA omega q) :
    (↑(r + s) : WithTop ℝ) ≤ omega (oppositeProductPivot p q - 1) := by
  have hp2 := (coe_le_halfTop_iff r (omega p.second)).mp hp
  have hq2 := (coe_le_halfTop_iff s (omega q.second)).mp hq
  have hp1 := Parameters.first_ge_of_second_ge omega hinv r p hp2
  have hq1 := Parameters.first_ge_of_second_ge omega hinv s q hq2
  have hfirst : (↑(r + s) : WithTop ℝ) ≤ omega (-p.first * c.bar q.first) := by
    rw [omega.map_mul, omega.map_neg, hinv, WithTop.coe_add]
    exact add_le_add hp1 hq1
  have hsecond : (↑(r + s) : WithTop ℝ) ≤ omega (p.second * q.second) := by
    rw [omega.map_mul]
    have hh := add_le_add hp2 hq2
    rw [← WithTop.coe_add] at hh
    exact (WithTop.coe_le_coe.mpr (by linarith : r + s ≤ 2 * r + 2 * s)).trans hh
  have he : oppositeProductPivot p q - 1 =
      -p.first * c.bar q.first + p.second * q.second := by
    unfold oppositeProductPivot
    ring
  rw [he]
  exact (le_min hfirst hsecond).trans (omega.map_add _ _)

/-- A positive ordinary depth sum also puts the commutator in the matrix big cell. -/
theorem oppositeProductPivot_ne_zero_of_depth_bounds
    (hinv : ∀ z : L, omega (c.bar z) = omega z)
    (p q : Parameters c) (r s : ℝ) (hrs : 0 < r + s)
    (hp : (r : WithTop ℝ) ≤ Parameters.depthA omega p)
    (hq : (s : WithTop ℝ) ≤ Parameters.depthA omega q) :
    oppositeProductPivot p q ≠ 0 := by
  have ht := value_oppositeProductPivot_sub_one_ge omega hinv p q r s hrs.le hp hq
  intro hzero
  rw [hzero, zero_sub, omega.map_neg, omega.map_one] at ht
  have he : r + s ≤ 0 := WithTop.coe_le_coe.mp ht
  linarith

/-- Positive lower depth bounds give actual commutator factors and the ordinary
diagonal congruence bound. -/
theorem exists_oppositeCommutator_factorization_of_depth_bounds
    (hinv : ∀ z : L, omega (c.bar z) = omega z)
    (p q : Parameters c) (r s : ℝ) (hrs : 0 < r + s)
    (hp : (r : WithTop ℝ) ≤ Parameters.depthA omega p)
    (hq : (s : WithTop ℝ) ≤ Parameters.depthA omega q) :
    ∃ (v' v : Parameters c) (t : Lˣ),
      oppositeCommutator p q =
        oppositeEmbedding c v' * diagonal c t * Parameters.embedding c v ∧
      (↑(r + s) : WithTop ℝ) ≤ omega ((t : L) - 1) := by
  let ht := oppositeProductPivot_ne_zero_of_depth_bounds omega hinv p q r s hrs hp hq
  refine ⟨q⁻¹ * oppositeProductLower p q ht, oppositeProductUpper p q ht * p⁻¹,
    Units.mk0 (oppositeProductPivot p q) ht, oppositeCommutator_factorization p q ht, ?_⟩
  exact value_oppositeProductPivot_sub_one_ge omega hinv p q r s hrs.le hp hq

/-- The pivot has the sharp doubled deviation value before any factors are constructed. -/
theorem value_oppositeProductPivot_sub_one_of_double (p q : Parameters c)
    (hdouble : p.first = 0 ∨ q.first = 0) :
    omega (oppositeProductPivot p q - 1) =
      doubleTop (Parameters.depthA omega p + Parameters.depthA omega q) := by
  rw [oppositeProductPivot_sub_one_of_double p q hdouble, omega.map_mul,
    doubleTop_depthA_add_depthA]

/-- A positive depth sum forces the doubled-input pivot to be nonzero. -/
theorem oppositeProductPivot_ne_zero_of_double_depth_sum
    (p q : Parameters c) (hdouble : p.first = 0 ∨ q.first = 0)
    (r : ℝ) (hr : 0 < r)
    (hdepth : Parameters.depthA omega p + Parameters.depthA omega q = (r : WithTop ℝ)) :
    oppositeProductPivot p q ≠ 0 := by
  have ht := value_oppositeProductPivot_sub_one_of_double omega p q hdouble
  rw [hdepth, doubleTop_coe] at ht
  intro hzero
  rw [hzero, zero_sub, omega.map_neg, omega.map_one] at ht
  have he : (0 : ℝ) = 2 * r := WithTop.coe_injective ht
  linarith

/-- Positive-depth doubled inputs admit actual big-cell commutator factors, whose
diagonal parameter has exactly twice the depth sum. -/
theorem exists_oppositeCommutator_factorization_of_double_depth_sum
    (p q : Parameters c) (hdouble : p.first = 0 ∨ q.first = 0)
    (r : ℝ) (hr : 0 < r)
    (hdepth : Parameters.depthA omega p + Parameters.depthA omega q = (r : WithTop ℝ)) :
    ∃ (v' v : Parameters c) (t : Lˣ),
      oppositeCommutator p q =
        oppositeEmbedding c v' * diagonal c t * Parameters.embedding c v ∧
      omega ((t : L) - 1) = (↑(2 * r) : WithTop ℝ) := by
  let ht := oppositeProductPivot_ne_zero_of_double_depth_sum omega p q hdouble r hr hdepth
  refine ⟨q⁻¹ * oppositeProductLower p q ht, oppositeProductUpper p q ht * p⁻¹,
    Units.mk0 (oppositeProductPivot p q) ht, oppositeCommutator_factorization p q ht, ?_⟩
  exact value_diagonal_sub_one_eq_double_of_depth_sum omega p q _ _ _ hdouble
    (oppositeCommutator_factorization p q ht) r hdepth

end Valuation

end Langlands.GroupScheme.SU3Root
