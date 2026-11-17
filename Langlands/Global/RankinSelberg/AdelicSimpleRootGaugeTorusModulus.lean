import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeTorusMellin

/-! # Positive-root modulus in block root coordinates -/

noncomputable section
universe u v
open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace GaugeTorusCoordinates

variable {G : Type v} [CommGroup G]

/-- The product of all positive-root values of a diagonal tuple. -/
def positiveRootProduct (t : ℕ) (d : Fin (t + 1) → G) : G :=
  ∏ i, ∏ j ∈ Finset.Ioi i, d i / d j

/-- Quotients of tail products consist of the intervening roots. -/
theorem tailProducts_div_tailProducts (t : ℕ) (a : Fin (t + 1) → G)
    (i j : Fin (t + 1)) (hij : i ≤ j) :
    tailProducts t a i / tailProducts t a j = ∏ k ∈ Finset.Ico i j, a k := by
  have hs : Finset.Ici j ⊆ Finset.Ici i := by
    intro k hk
    exact Finset.mem_Ici.mpr (hij.trans (Finset.mem_Ici.mp hk))
  have he : Finset.Ici i \ Finset.Ici j = Finset.Ico i j := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Ici, Finset.mem_Ico, not_le]
  simpa only [he, tailProducts] using
    (Finset.prod_sdiff_eq_div (f := a) hs).symm

/-- A simple root occurs in exactly `(k+1)*(t-k)` positive roots. -/
theorem positiveRootProduct_tailProducts (t : ℕ) (a : Fin (t + 1) → G) :
    positiveRootProduct t (tailProducts t a) =
      ∏ k, a k ^ (((k : ℕ) + 1) * (t - (k : ℕ))) := by
  have hp (i j : Fin (t + 1)) :
      (if i < j then tailProducts t a i / tailProducts t a j else 1) =
        ∏ k ∈ Finset.Ico i j, a k := by
    by_cases hij : i < j
    · rw [ite_eq_left hij, tailProducts_div_tailProducts t a i j hij.le]
    · simp only [ite_eq_right hij, Finset.Ico_eq_empty hij, Finset.prod_empty]
  calc
    _ = ∏ i, ∏ j, ∏ k ∈ Finset.Ico i j, a k := by
      simp only [positiveRootProduct, ← Finset.filter_lt_eq_Ioi]
      simp_rw [Finset.prod_filter, hp]
    _ = ∏ i, ∏ k, ∏ j, if i ≤ k ∧ k < j then a k else 1 := by
      simp only [← Finset.filter_le_lt_eq_Ico]
      simp_rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.prod_comm]
    _ = ∏ k, ∏ i, ∏ j, if i ≤ k ∧ k < j then a k else 1 :=
      Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k _
      simp_rw [ite_and, Finset.prod_ite_irrel, Finset.prod_const_one,
        ← Finset.prod_filter]
      simp only [Finset.filter_lt_eq_Ioi, Finset.filter_ge_eq_Iic,
        Finset.prod_const, Fin.card_Ioi, Fin.card_Iic, ← pow_mul,
        Nat.add_sub_cancel]
      rw [Nat.mul_comm]

/-- All positive roots are products of adjacent block roots; the final
diagonal root has multiplicity zero. -/
theorem positiveRootProduct_eq_prod_blockRoots_pow (t : ℕ)
    (d : Fin (t + 1) → G) :
    positiveRootProduct t d =
      ∏ k, blockRoots t d k ^ (((k : ℕ) + 1) * (t - (k : ℕ))) := by
  simpa only [tailProducts_blockRoots] using
    positiveRootProduct_tailProducts t (blockRoots t d)

end GaugeTorusCoordinates

variable (F : Type u) [Field F] [NumberField F]

/-- The product of the full idele norms of all positive diagonal roots. -/
def gaugeDiagonalModulus (t : ℕ) (d : Fin (t + 1) → Ideles F) : ℝ :=
  ∏ i, ∏ j ∈ Finset.Ioi i,
    ((IdeleAbsoluteValue.full F (d i / d j) : ℝ≥0) : ℝ)

/-- The fixed exponent contributed by the inverse positive-root modulus. -/
def gaugeInverseModulusRootExponent (t : ℕ) (j : Fin (t + 1)) : ℝ :=
  -((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ)

theorem gaugeDiagonalModulus_pos (t : ℕ) (d : Fin (t + 1) → Ideles F) :
    0 < gaugeDiagonalModulus F t d :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ =>
    IdeleAbsoluteValue.full_pos F _

/-- The actual positive-root norm product has the counted root multiplicities. -/
theorem gaugeDiagonalModulus_eq_blockRoots (t : ℕ)
    (d : Fin (t + 1) → Ideles F) :
    gaugeDiagonalModulus F t d =
      ∏ j, ((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
        (((j : ℕ) + 1) * (t - (j : ℕ))) := by
  have hp := congrArg
    (fun a : Ideles F => ((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ))
    (GaugeTorusCoordinates.positiveRootProduct_eq_prod_blockRoots_pow t d)
  simpa only [GaugeTorusCoordinates.positiveRootProduct, gaugeDiagonalModulus,
    gaugeBlockRootIdeles, map_prod, map_pow, Units.coe_prod,
    Units.val_pow_eq_pow_val, NNReal.coe_prod, NNReal.coe_pow] using hp

/-- The inverse modulus is the product of the fixed negative real root powers. -/
theorem gaugeDiagonalModulus_inv_eq (t : ℕ) (d : Fin (t + 1) → Ideles F) :
    (gaugeDiagonalModulus F t d)⁻¹ =
      ∏ j, ((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
        gaugeInverseModulusRootExponent t j := by
  rw [gaugeDiagonalModulus_eq_blockRoots, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [gaugeInverseModulusRootExponent,
    Real.rpow_neg (IdeleAbsoluteValue.full_pos F _).le, Real.rpow_natCast]

theorem ofReal_gaugeDiagonalModulus_inv (t : ℕ)
    (d : Fin (t + 1) → Ideles F) :
    ENNReal.ofReal (gaugeDiagonalModulus F t d)⁻¹ =
      ∏ j, ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
          gaugeInverseModulusRootExponent t j) := by
  rw [gaugeDiagonalModulus_inv_eq, ENNReal.ofReal_prod_of_nonneg]
  intro j _
  exact Real.rpow_nonneg (IdeleAbsoluteValue.full_pos F _).le _

local instance torusModulusSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance torusModulusSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance torusModulusIdeleMeasurableSpace : MeasurableSpace (Ideles F) := borel _
local instance torusModulusIdeleBorelSpace : BorelSpace (Ideles F) := ⟨rfl⟩

/-- Padded torus convergence with the inverse positive-root modulus. This
statement does not assume an identification with any quotient measure. -/
theorem IsAdelicSimpleRootGauge.lintegral_padded_torus_mul_inverseModulus_of_large
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (mu : Measure (Fin (t + 1) → Ideles F)) [Measure.IsHaarMeasure mu]
    {σ : ℝ}
    (hσ : τ + 3 + ∑ j : Fin (t + 1),
      ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) < σ) :
    ∫⁻ d : Fin (t + 1) → Ideles F,
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
        (gaugeDiagonalPoint F (t + 1) d)) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ σ) *
        ENNReal.ofReal (gaugeDiagonalModulus F t d)⁻¹
      ∂mu < ⊤ := by
  simp_rw [ofReal_gaugeDiagonalModulus_inv]
  apply hΞ.lintegral_padded_torus_mul_rootWeights_of_large F h mu
    (gaugeInverseModulusRootExponent t)
  have habs (j : Fin (t + 1)) :
      |gaugeInverseModulusRootExponent t j| =
        ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) := by
    rw [gaugeInverseModulusRootExponent, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤
        ((((j : ℕ) + 1) * (t - (j : ℕ)) : ℕ) : ℝ) from Nat.cast_nonneg _)]
  simpa only [habs] using hσ

end Langlands.Global.RankinSelbergGlobal
