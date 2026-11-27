import Langlands.BaseChange.TwistedLocalDescent.MatrixNorm

/-! # The twisted conjugation chart near a Levi point and its linear part

For a block shape `B`, a matrix `X = X_𝔭 + X_𝔲̄` (block upper and strictly block lower parts), an
invertible `d` and an isometric ring automorphism `σ` of an ultrametric field, the chart
`χ(X) = d⁻¹ (1 + X_𝔲̄)⁻¹ d (1 + X_𝔭) σ(1 + X_𝔲̄) − 1` differs from its linear part
`X_𝔭 + σ(X_𝔲̄) − d⁻¹ X_𝔲̄ d` by a map of Lipschitz constant `≤ κ r` on the ball of radius
`r ≤ 1`, with `κ = max(‖d‖ ‖d⁻¹‖, 1)`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear

universe v

attribute [local instance] Matrix.normedAddCommGroup matrix_isUltrametricDist

variable {𝕂 : Type v} [NormedField 𝕂] {n : ℕ} (B : BlockShape n)

/-- The strictly block lower part. -/
def lowerPart (X : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  Matrix.of fun a b => if B.coordinateBlock b < B.coordinateBlock a then X a b else 0

/-- The block upper part (diagonal blocks included). -/
def upperPart (X : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 := X - lowerPart B X

theorem lowerPart_isLower (X : Matrix (Fin n) (Fin n) 𝕂) :
    ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → lowerPart B X a b = 0 := by
  intro a b h
  simp [lowerPart, not_lt.mpr h]

theorem lowerPart_sub (X Y : Matrix (Fin n) (Fin n) 𝕂) : lowerPart B X - lowerPart B Y = lowerPart B (X - Y) := by
  ext a b
  simp only [lowerPart, Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem upperPart_sub (X Y : Matrix (Fin n) (Fin n) 𝕂) : upperPart B X - upperPart B Y = upperPart B (X - Y) := by
  simp only [upperPart, ← lowerPart_sub]
  abel

theorem norm_lowerPart_le (X : Matrix (Fin n) (Fin n) 𝕂) : ‖lowerPart B X‖ ≤ ‖X‖ := by
  rw [Matrix.norm_le_iff (norm_nonneg _)]
  intro a b
  simp only [lowerPart, Matrix.of_apply]
  split_ifs
  · exact Matrix.norm_entry_le_entrywise_sup_norm X
  · simp

theorem norm_upperPart_le (X : Matrix (Fin n) (Fin n) 𝕂) : ‖upperPart B X‖ ≤ ‖X‖ := by
  rw [Matrix.norm_le_iff (norm_nonneg _)]
  intro a b
  simp only [upperPart, lowerPart, Matrix.sub_apply, Matrix.of_apply]
  split_ifs
  · simp
  · simpa using Matrix.norm_entry_le_entrywise_sup_norm X

theorem norm_mul_sub_mul_le [IsUltrametricDist 𝕂] (p q p' q' : Matrix (Fin n) (Fin n) 𝕂) :
    ‖p * q - p' * q'‖ ≤ max (‖p - p'‖ * ‖q‖) (‖p'‖ * ‖q - q'‖) := by
  have : p * q - p' * q' = (p - p') * q + p' * (q - q') := by noncomm_ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · exact matrix_norm_mul_le _ _
  · exact matrix_norm_mul_le _ _

variable (σ : 𝕂 →+* 𝕂) (d dinv : Matrix (Fin n) (Fin n) 𝕂)

/-- The chart `X ↦ d⁻¹ (1 + X_𝔲̄)⁻¹ d (1 + X_𝔭) σ(1 + X_𝔲̄) − 1`. -/
def twistedChart (X : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  dinv * lowerInverse B (lowerPart B X) * d * (1 + upperPart B X) *
    (1 + lowerPart B X).map σ - 1

/-- The linear part `X ↦ X_𝔭 + σ(X_𝔲̄) − d⁻¹ X_𝔲̄ d`. -/
def twistedChartLinear (X : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  upperPart B X + (lowerPart B X).map σ - dinv * lowerPart B X * d

/-- The remainder of the chart. -/
def twistedChartRemainder (X : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 := twistedChart B σ d dinv X - twistedChartLinear B σ d dinv X

theorem map_one_add (Z : Matrix (Fin n) (Fin n) 𝕂) : (1 + Z).map σ = 1 + Z.map σ := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, map_add, Matrix.one_apply]
  split_ifs <;> simp

/-- The algebraic form of the remainder. -/
theorem twistedChartRemainder_eq (hd : dinv * d = 1) (X : Matrix (Fin n) (Fin n) 𝕂) :
    let Z := lowerPart B X
    let W := upperPart B X
    let g := lowerInverse B Z
    let α := -(dinv * Z * g * d)
    let γ := Z.map σ
    twistedChartRemainder B σ d dinv X =
      dinv * (Z * Z * g) * d + α * W + α * γ + W * γ + α * W * γ := by
  intro Z W g α γ
  have hg : g = 1 - Z * g := by
    have h := one_add_mul_lowerInverse B (lowerPart_isLower B X)
    calc g = (1 + Z) * g - Z * g := by noncomm_ring
      _ = 1 - Z * g := by rw [h]
  have ha : dinv * g * d = 1 + α := by
    simp only [α]
    calc dinv * g * d = dinv * (1 - Z * g) * d := by rw [← hg]
      _ = dinv * d - dinv * Z * g * d := by noncomm_ring
      _ = 1 + -(dinv * Z * g * d) := by rw [hd]; abel
  have hZg : dinv * Z * g * d = dinv * Z * d - dinv * (Z * Z * g) * d := by
    calc dinv * Z * g * d = dinv * Z * (1 - Z * g) * d := by rw [← hg]
      _ = dinv * Z * d - dinv * (Z * Z * g) * d := by noncomm_ring
  simp only [twistedChartRemainder, twistedChart, twistedChartLinear]
  rw [show dinv * lowerInverse B (lowerPart B X) * d = 1 + α from ha, map_one_add]
  change (1 + α) * (1 + W) * (1 + γ) - 1 - (W + γ - dinv * Z * d) = _
  have hα : α = -(dinv * Z * d) + dinv * (Z * Z * g) * d := by
    simp only [α, hZg]
    abel
  rw [hα]
  noncomm_ring

section Estimate

variable [IsUltrametricDist 𝕂]

theorem norm_lowerInverse_sub_le {X Y : Matrix (Fin n) (Fin n) 𝕂} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖lowerInverse B (lowerPart B X) - lowerInverse B (lowerPart B Y)‖ ≤ ‖X - Y‖ := by
  set gX := lowerInverse B (lowerPart B X)
  set gY := lowerInverse B (lowerPart B Y)
  have h1 : gX * (1 + lowerPart B X) = 1 := lowerInverse_mul_one_add B (lowerPart_isLower B X)
  have h2 : (1 + lowerPart B Y) * gY = 1 := one_add_mul_lowerInverse B (lowerPart_isLower B Y)
  have hres : gX - gY = gX * (lowerPart B Y - lowerPart B X) * gY := by
    calc gX - gY = gX * ((1 + lowerPart B Y) * gY) - (gX * (1 + lowerPart B X)) * gY := by
          rw [h1, h2, mul_one, one_mul]
      _ = gX * (lowerPart B Y - lowerPart B X) * gY := by noncomm_ring
  have hgX : ‖gX‖ ≤ 1 := norm_lowerInverse_le B ((norm_lowerPart_le B X).trans hX)
  have hgY : ‖gY‖ ≤ 1 := norm_lowerInverse_le B ((norm_lowerPart_le B Y).trans hY)
  rw [hres]
  calc ‖gX * (lowerPart B Y - lowerPart B X) * gY‖ ≤
        ‖gX‖ * ‖lowerPart B Y - lowerPart B X‖ * ‖gY‖ :=
        (matrix_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (matrix_norm_mul_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * ‖X - Y‖ * 1 := by
        gcongr
        rw [lowerPart_sub]
        exact (norm_lowerPart_le B _).trans (norm_sub_rev _ _).le
    _ = ‖X - Y‖ := by ring

/-- **Lipschitz estimate for the remainder of the chart.** -/
theorem norm_twistedChartRemainder_sub_le (hσ : ∀ a, ‖σ a‖ = ‖a‖) (hd : dinv * d = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {X Y : Matrix (Fin n) (Fin n) 𝕂} (hX : ‖X‖ ≤ r)
    (hY : ‖Y‖ ≤ r) :
    ‖twistedChartRemainder B σ d dinv X - twistedChartRemainder B σ d dinv Y‖ ≤
      max (‖dinv‖ * ‖d‖) 1 * r * ‖X - Y‖ := by
  set κ := max (‖dinv‖ * ‖d‖) 1
  set δ := ‖X - Y‖
  have hκ1 : 1 ≤ κ := le_max_right _ _
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ1
  have hδ : 0 ≤ δ := norm_nonneg _
  have hconj : ∀ M : Matrix (Fin n) (Fin n) 𝕂, ‖dinv * M * d‖ ≤ κ * ‖M‖ := fun M =>
    calc ‖dinv * M * d‖ ≤ ‖dinv‖ * ‖M‖ * ‖d‖ :=
          (matrix_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (matrix_norm_mul_le _ _)
            (norm_nonneg _))
      _ = (‖dinv‖ * ‖d‖) * ‖M‖ := by ring
      _ ≤ κ * ‖M‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hmul := fun p q p' q' => norm_mul_sub_mul_le (𝕂 := 𝕂) (n := n) p q p' q'
  -- Bounds for the pieces.
  set ZX := lowerPart B X
  set ZY := lowerPart B Y
  set WX := upperPart B X
  set WY := upperPart B Y
  set gX := lowerInverse B ZX
  set gY := lowerInverse B ZY
  have hZX : ‖ZX‖ ≤ r := (norm_lowerPart_le B X).trans hX
  have hZY : ‖ZY‖ ≤ r := (norm_lowerPart_le B Y).trans hY
  have hWX : ‖WX‖ ≤ r := (norm_upperPart_le B X).trans hX
  have hWY : ‖WY‖ ≤ r := (norm_upperPart_le B Y).trans hY
  have hgX : ‖gX‖ ≤ 1 := norm_lowerInverse_le B (hZX.trans hr1)
  have hgY : ‖gY‖ ≤ 1 := norm_lowerInverse_le B (hZY.trans hr1)
  have hdZ : ‖ZX - ZY‖ ≤ δ := by rw [lowerPart_sub]; exact norm_lowerPart_le B _
  have hdW : ‖WX - WY‖ ≤ δ := by rw [upperPart_sub]; exact norm_upperPart_le B _
  have hdg : ‖gX - gY‖ ≤ δ := norm_lowerInverse_sub_le B (hX.trans hr1) (hY.trans hr1)
  have hγX : ‖ZX.map σ‖ ≤ r := by rw [matrix_norm_map_eq _ _ hσ]; exact hZX
  have hγY : ‖ZY.map σ‖ ≤ r := by rw [matrix_norm_map_eq _ _ hσ]; exact hZY
  have hdγ : ‖ZX.map σ - ZY.map σ‖ ≤ δ := by
    have : ZX.map σ - ZY.map σ = (ZX - ZY).map σ := by
      ext a b
      simp [map_sub]
    rw [this, matrix_norm_map_eq _ _ hσ]
    exact hdZ
  have hZg : ‖ZX * gX - ZY * gY‖ ≤ δ := by
    refine (hmul _ _ _ _).trans (max_le ?_ ?_)
    · calc ‖ZX - ZY‖ * ‖gX‖ ≤ δ * 1 := by gcongr
        _ = δ := mul_one δ
    · calc ‖ZY‖ * ‖gX - gY‖ ≤ 1 * δ := by gcongr; exact hZY.trans hr1
        _ = δ := one_mul δ
  have hαX : ‖-(dinv * ZX * gX * d)‖ ≤ κ * r := by
    rw [norm_neg, show dinv * ZX * gX * d = dinv * (ZX * gX) * d by noncomm_ring]
    refine (hconj _).trans (mul_le_mul_of_nonneg_left ?_ hκ0)
    calc ‖ZX * gX‖ ≤ ‖ZX‖ * ‖gX‖ := matrix_norm_mul_le _ _
      _ ≤ r * 1 := by gcongr
      _ = r := mul_one r
  have hαY : ‖-(dinv * ZY * gY * d)‖ ≤ κ * r := by
    rw [norm_neg, show dinv * ZY * gY * d = dinv * (ZY * gY) * d by noncomm_ring]
    refine (hconj _).trans (mul_le_mul_of_nonneg_left ?_ hκ0)
    calc ‖ZY * gY‖ ≤ ‖ZY‖ * ‖gY‖ := matrix_norm_mul_le _ _
      _ ≤ r * 1 := by gcongr
      _ = r := mul_one r
  have hdα : ‖-(dinv * ZX * gX * d) - -(dinv * ZY * gY * d)‖ ≤ κ * δ := by
    rw [show -(dinv * ZX * gX * d) - -(dinv * ZY * gY * d) =
      -(dinv * (ZX * gX - ZY * gY) * d) by noncomm_ring, norm_neg]
    exact (hconj _).trans (mul_le_mul_of_nonneg_left hZg hκ0)
  have hadd : ∀ (a b : Matrix (Fin n) (Fin n) 𝕂) (C : ℝ), ‖a‖ ≤ C → ‖b‖ ≤ C → ‖a + b‖ ≤ C :=
    fun a b C ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  have hZgX : ‖ZX * gX‖ ≤ r := (matrix_norm_mul_le _ _).trans
    (by nlinarith [norm_nonneg ZX, norm_nonneg gX])
  set αX := -(dinv * ZX * gX * d)
  set αY := -(dinv * ZY * gY * d)
  set γX := ZX.map σ
  set γY := ZY.map σ
  have hrδ : r * δ ≤ κ * r * δ := by
    have := mul_le_mul_of_nonneg_right hκ1 (mul_nonneg hr0 hδ)
    linarith [this]
  -- The five differences.
  have h1 : ‖dinv * (ZX * ZX * gX) * d - dinv * (ZY * ZY * gY) * d‖ ≤ κ * r * δ := by
    rw [show dinv * (ZX * ZX * gX) * d - dinv * (ZY * ZY * gY) * d =
      dinv * (ZX * (ZX * gX) - ZY * (ZY * gY)) * d by noncomm_ring]
    refine (hconj _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hmul _ _ _ _).trans (max_le ?_ ?_)) hκ0
    · calc ‖ZX - ZY‖ * ‖ZX * gX‖ ≤ δ * r := by gcongr
        _ = r * δ := mul_comm _ _
    · gcongr
  have h2 : ‖αX * WX - αY * WY‖ ≤ κ * r * δ := by
    refine (hmul _ _ _ _).trans (max_le ?_ ?_)
    · calc ‖αX - αY‖ * ‖WX‖ ≤ (κ * δ) * r := by gcongr
        _ = κ * r * δ := by ring
    · gcongr
  have h3 : ‖αX * γX - αY * γY‖ ≤ κ * r * δ := by
    refine (hmul _ _ _ _).trans (max_le ?_ ?_)
    · calc ‖αX - αY‖ * ‖γX‖ ≤ (κ * δ) * r := by gcongr
        _ = κ * r * δ := by ring
    · gcongr
  have h4 : ‖WX * γX - WY * γY‖ ≤ κ * r * δ := by
    refine (hmul _ _ _ _).trans (max_le ?_ ?_)
    · calc ‖WX - WY‖ * ‖γX‖ ≤ δ * r := by gcongr
        _ ≤ κ * r * δ := by rw [mul_comm]; exact hrδ
    · calc ‖WY‖ * ‖γX - γY‖ ≤ r * δ := by gcongr
        _ ≤ κ * r * δ := hrδ
  have hαWY : ‖αY * WY‖ ≤ κ * r := by
    calc ‖αY * WY‖ ≤ ‖αY‖ * ‖WY‖ := matrix_norm_mul_le _ _
      _ ≤ (κ * r) * 1 := mul_le_mul hαY (hWY.trans hr1) (norm_nonneg _) (by positivity)
      _ = κ * r := mul_one _
  have h5 : ‖αX * WX * γX - αY * WY * γY‖ ≤ κ * r * δ := by
    refine (hmul _ _ _ _).trans (max_le ?_ ?_)
    · calc ‖αX * WX - αY * WY‖ * ‖γX‖ ≤ (κ * r * δ) * 1 :=
          mul_le_mul h2 (hγX.trans hr1) (norm_nonneg _) (by positivity)
        _ = κ * r * δ := mul_one _
    · gcongr
  rw [twistedChartRemainder_eq B σ d dinv hd X, twistedChartRemainder_eq B σ d dinv hd Y]
  change ‖dinv * (ZX * ZX * gX) * d + αX * WX + αX * γX + WX * γX + αX * WX * γX -
    (dinv * (ZY * ZY * gY) * d + αY * WY + αY * γY + WY * γY + αY * WY * γY)‖ ≤ κ * r * δ
  rw [show dinv * (ZX * ZX * gX) * d + αX * WX + αX * γX + WX * γX + αX * WX * γX -
      (dinv * (ZY * ZY * gY) * d + αY * WY + αY * γY + WY * γY + αY * WY * γY) =
      (dinv * (ZX * ZX * gX) * d - dinv * (ZY * ZY * gY) * d) + (αX * WX - αY * WY) +
        (αX * γX - αY * γY) + (WX * γX - WY * γY) + (αX * WX * γX - αY * WY * γY) by abel]
  exact hadd _ _ _ (hadd _ _ _ (hadd _ _ _ (hadd _ _ _ h1 h2) h3) h4) h5

end Estimate

end Langlands.BaseChange.TwistedLocalDescent
