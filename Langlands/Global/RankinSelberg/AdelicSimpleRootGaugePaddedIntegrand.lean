import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeCompactPadding
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeTorusCoordinates

/-! # The padded gauge integrand in block-root coordinates -/

noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace GaugeCoordinateRestriction

/-- Insert fixed coordinates equal to one after the given coordinates. -/
def extendByOne {A : Type v} [One A] {m n : ℕ} (x : Fin m → A) : Fin n → A :=
  fun i => if hi : (i : ℕ) < m then x ⟨i, hi⟩ else 1

@[simp]
theorem extendByOne_castLE {A : Type v} [One A] {m n : ℕ} (h : m ≤ n)
    (x : Fin m → A) (i : Fin m) : extendByOne x (Fin.castLE h i) = x i := by
  simp [extendByOne, i.isLt]

theorem continuous_extendByOne {A : Type v} [One A] [TopologicalSpace A] (m n : ℕ) :
    Continuous (@extendByOne A _ m n) := by
  apply continuous_pi
  intro i
  by_cases hi : (i : ℕ) < m
  · simpa only [extendByOne, dite_eq_left hi] using
      (continuous_apply (⟨i, hi⟩ : Fin m) : Continuous (fun x : Fin m → A => x ⟨i, hi⟩))
  · simpa only [extendByOne, dite_eq_right hi] using
      (continuous_const : Continuous (fun _ : Fin m → A => (1 : A)))

theorem isClosedEmbedding_extendByOne {A : Type v} [One A] [TopologicalSpace A]
    [T2Space A] {m n : ℕ} (h : m ≤ n) :
    Topology.IsClosedEmbedding (@extendByOne A _ m n) := by
  let take : (Fin n → A) → (Fin m → A) := fun y i => y (Fin.castLE h i)
  have htake : Continuous take := continuous_pi fun i => continuous_apply (Fin.castLE h i)
  have hleft : Function.LeftInverse take (@extendByOne A _ m n) := by
    intro x
    funext i
    exact extendByOne_castLE h x i
  exact hleft.isClosedEmbedding htake (continuous_extendByOne m n)

/-- The scalar determinant and gauge weights separate coordinate by coordinate. -/
theorem prod_rpow_weight {I : Type v} [Fintype I] (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (w : I → ℕ) (σ τ : ℝ) :
    (∏ i, a i) ^ (-τ) * (∏ i, a i ^ w i) ^ σ =
      ∏ i, a i ^ ((w i : ℝ) * σ - τ) := by
  rw [← Real.finsetProd_rpow _ _ (fun i _ => (ha i).le),
    ← Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (ha i).le _),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_natCast_mul (ha i).le]
  rw [← Real.rpow_add (ha i)]
  congr 1
  ring

end GaugeCoordinateRestriction

variable (F : Type u) [Field F] [NumberField F]

/-- Regard all block roots, including the last diagonal entry, as an additive row. -/
def gaugeBlockRootRow (t : ℕ) (d : Fin (t + 1) → Ideles F) : RowVector F (t + 1) :=
  fun _ j => (gaugeBlockRootIdeles F t d j : Adeles F)

/-- Fill the remaining ambient simple-root coordinates by ones. -/
def gaugeExtendRootRow {m n : ℕ} (x : RowVector F m) : RowVector F n :=
  fun _ => GaugeCoordinateRestriction.extendByOne (x 0)

/-- The ambient root row of a padded diagonal is the block root row followed by ones. -/
theorem gaugeSimpleRootRow_padded {t r : ℕ} (h : t < r)
    (d : Fin (t + 1) → Ideles F) :
    gaugeSimpleRootRow F r (gaugePaddedIdeles F d) =
      gaugeExtendRootRow F (gaugeBlockRootRow F t d) := by
  ext k i
  rw [gaugeSimpleRootRow, gaugeSimpleRootIdeles_padded F h]
  by_cases hi : (i : ℕ) < t + 1
  · simp only [gaugeExtendRootRow, GaugeCoordinateRestriction.extendByOne, dite_eq_left hi,
      gaugeBlockRootRow, gaugeBlockRootIdeles]
    by_cases ht : (i : ℕ) < t
    · have he : (⟨i, hi⟩ : Fin (t + 1)) = (⟨i, ht⟩ : Fin t).castSucc := rfl
      rw [he, GaugeTorusCoordinates.blockRoots_castSucc]
      simp only [dite_eq_left ht, gaugeSimpleRootIdeles]
    · have hit : (i : ℕ) = t := by omega
      have he : (⟨i, hi⟩ : Fin (t + 1)) = Fin.last t := Fin.ext hit
      rw [he, GaugeTorusCoordinates.blockRoots_last]
      simp only [dite_eq_right ht, ite_eq_left hit]
  · have ht : ¬(i : ℕ) < t := by omega
    have hit : ¬(i : ℕ) = t := by omega
    simp [gaugeExtendRootRow, GaugeCoordinateRestriction.extendByOne, hi, ht, hit]

/-- The first diagonal idele is the product of all block roots. -/
theorem prod_gaugeBlockRootIdeles (t : ℕ) (d : Fin (t + 1) → Ideles F) :
    ∏ j, gaugeBlockRootIdeles F t d j = d 0 := by
  have hi := congrFun (GaugeTorusCoordinates.tailProducts_blockRoots t d) 0
  simpa [GaugeTorusCoordinates.tailProducts, gaugeBlockRootIdeles] using hi

/-- The ambient gauge norm product becomes the product of the active block root norms. -/
theorem gaugeSimpleRootNormProduct_padded_blockRoots {t r : ℕ} (h : t < r)
    (d : Fin (t + 1) → Ideles F) :
    gaugeSimpleRootNormProduct F r (gaugePaddedIdeles F d) =
      ∏ j, ((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) := by
  rw [gaugeSimpleRootNormProduct_padded F h, ← prod_gaugeBlockRootIdeles F t d,
    map_prod, Units.coe_prod, NNReal.coe_prod]

/-- On a proper padded diagonal, the two scalar weights have root exponents
`(j + 1) * σ - τ`. -/
theorem gaugePadded_scalarWeight {t r : ℕ} (h : t < r)
    (d : Fin (t + 1) → Ideles F) (σ τ : ℝ) :
    ENNReal.ofReal (gaugeSimpleRootNormProduct F r (gaugePaddedIdeles F d) ^ (-τ)) *
        ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) d) ^ σ) =
      ∏ j, ENNReal.ofReal
        (((IdeleAbsoluteValue.full F (gaugeBlockRootIdeles F t d j) : ℝ≥0) : ℝ) ^
          ((((j : ℕ) + 1 : ℕ) : ℝ) * σ - τ)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by
      rw [gaugeSimpleRootNormProduct_padded F h]
      exact (IdeleAbsoluteValue.full_pos F _).le) _),
    gaugeSimpleRootNormProduct_padded_blockRoots F h,
    detNorm_gaugeDiagonalPoint_blockRoots,
    GaugeCoordinateRestriction.prod_rpow_weight (I := Fin (t + 1)) _
      (fun j => IdeleAbsoluteValue.full_pos F _) (fun j => (j : ℕ) + 1)]
  exact ENNReal.ofReal_prod_of_nonneg fun j _ => Real.rpow_nonneg (by positivity) _

end Langlands.Global.RankinSelbergGlobal
