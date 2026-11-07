import Langlands.Representation.RankinSelberg.CauchyDegreeIndex
import Langlands.Representation.RankinSelberg.SymmetricAlternantBridge

/-! # Formal Schur expansion by the Cauchy determinant -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

/-- The integral weight underlying a finite degree partition. -/
def degreePartitionWeight {n d : ℕ} (α : DegreePartition n d) : Fin (n + 1) → ℤ :=
  fun i => (α.val i).val

theorem degreePartitionWeight_nonneg {n d : ℕ} (α : DegreePartition n d) :
    ∀ i, 0 ≤ degreePartitionWeight α i := fun _ => Nat.cast_nonneg _

theorem degreePartitionWeight_antitone {n d : ℕ} (α : DegreePartition n d) :
    Antitone (degreePartitionWeight α) := by
  intro i j hij
  change ((α.val j).val : ℤ) ≤ ((α.val i).val : ℤ)
  exact_mod_cast α.property.1 hij

variable {R : Type*} [CommRing R]

/-- The finite alternant coefficient sum in a fixed partition degree. -/
def cauchyPartitionCoefficient {n : ℕ} (H : PowerSeries R) (y : Fin (n + 1) → R)
    (d : ℕ) : R :=
  ∑ α : DegreePartition n d, seriesJacobiTrudi H (degreePartitionWeight α) *
    Matrix.det (weightMonomialMatrix y (degreePartitionWeight α))

theorem exponentPartition_degreePartitionSubset {n d : ℕ} (α : DegreePartition n d) :
    exponentPartition (fun i =>
      ((degreePartitionSubset α).val.orderEmbOfFin (degreePartitionSubset α).property i).val) =
      degreePartitionWeight α := by
  rw [degreePartitionSubset_orderEmb]
  funext i
  change (((degreePartitionNatExponents α i.rev : ℕ) : ℤ) - i.rev.val) = (α.val i).val
  simp only [degreePartitionNatExponents, Fin.rev_rev]
  omega

/-- The shifted determinant coefficient is the finite partition alternant sum. -/
theorem coeff_det_eq_cauchyPartitionCoefficient {n : ℕ}
    (H : PowerSeries R) (y : Fin (n + 1) → R) (d : ℕ) :
    PowerSeries.coeff (d + staircaseDegree n) (Matrix.det (seriesAlternantMatrix H y)) =
      cauchyPartitionCoefficient H y d := by
  classical
  let L := d + staircaseDegree n
  let F : {S : Finset (Fin (L + 1)) // S.card = n + 1} → R := fun S =>
    Matrix.det (seriesCoefficientMinor H (fun i => (S.val.orderEmbOfFin S.property i).val)) *
      Matrix.det (monomialMinor y (fun i => (S.val.orderEmbOfFin S.property i).val))
  calc
    _ = ∑ S : {S : Finset (Fin (L + 1)) // S.card = n + 1},
        if L = ∑ i, (S.val.orderEmbOfFin S.property i).val then F S else 0 :=
      coeff_det_seriesAlternantMatrix_eq_minor_sum H y L L le_rfl
    _ = ∑ S : DegreeSubset n d, F S.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun S => by simp [L, eq_comm]) F
    _ = ∑ α : DegreePartition n d, F (degreePartitionToSubset α).val :=
      (Equiv.sum_comp (degreePartitionSubsetEquiv n d) (fun S => F S.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro α _
      dsimp [F]
      rw [minor_product_eq_partition]
      change seriesJacobiTrudi H (exponentPartition (fun i =>
          ((degreePartitionSubset α).val.orderEmbOfFin (degreePartitionSubset α).property i).val)) *
        Matrix.det (weightMonomialMatrix y (exponentPartition (fun i =>
          ((degreePartitionSubset α).val.orderEmbOfFin (degreePartitionSubset α).property i).val))) = _
      rw [exponentPartition_degreePartitionSubset]

/-- The base alternant multiplies the ordinary rescaled-product coefficient. -/
theorem baseAlternant_mul_coeff_rescaled {n : ℕ} (H : PowerSeries R)
    (y : Fin (n + 1) → R) (d : ℕ) :
    Matrix.det (reverseVandermonde y) *
      PowerSeries.coeff d (∏ j : Fin (n + 1), PowerSeries.rescale (y j) H) =
      cauchyPartitionCoefficient H y d := by
  rw [← coeff_det_eq_cauchyPartitionCoefficient, det_seriesAlternantMatrix]
  let P := ∏ j : Fin (n + 1), PowerSeries.rescale (y j) H
  have hmul (a : R) (k : ℕ) :
      PowerSeries.X ^ k * PowerSeries.C a * P =
        PowerSeries.C a * (PowerSeries.X ^ k * P) := by ring
  rw [hmul, PowerSeries.coeff_C_mul, staircaseDegree, PowerSeries.coeff_X_pow_mul]

/-- The reversed generic Vandermonde is the published zero-weight alternant. -/
theorem reverseVandermonde_variables (A : Type*) [CommRing A] (n : ℕ) :
    reverseVandermonde (fun j : Fin (n + 1) => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A)) =
      alternantMatrix A (0 : Fin (n + 1) → ℤ) := by
  apply Matrix.ext
  intro i j
  simp only [reverseVandermonde, alternantMatrix, Matrix.of_apply, Pi.zero_apply]
  congr 1
  have hi := i.add_rev_cast
  omega

/-- The formal Schur coefficient identity for an arbitrary input series. -/
theorem formal_cauchy_coeff (A : Type*) [CommRing A] [IsDomain A] {n : ℕ}
    (H : PowerSeries (MvPolynomial (Fin (n + 1)) A)) (d : ℕ) :
    PowerSeries.coeff d
      (∏ j : Fin (n + 1), PowerSeries.rescale (MvPolynomial.X j) H) =
      ∑ α : DegreePartition n d,
        seriesJacobiTrudi H (degreePartitionWeight α) * jacobiTrudi A (degreePartitionWeight α) := by
  let D := Matrix.det (alternantMatrix A (0 : Fin (n + 1) → ℤ))
  have hD : D ≠ 0 := by
    dsimp [D]
    rw [← det_erasedCoefficientMatrix]
    exact det_erasedCoefficientMatrix_ne_zero n
  have hfactor := baseAlternant_mul_coeff_rescaled H
    (fun j : Fin (n + 1) => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A)) d
  rw [reverseVandermonde_variables] at hfactor
  have hAlt (α : DegreePartition n d) :
      Matrix.det (weightMonomialMatrix
        (fun j : Fin (n + 1) => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A))
        (degreePartitionWeight α)) = jacobiTrudi A (degreePartitionWeight α) * D :=
    (jacobiTrudi_mul_baseAlternant (degreePartitionWeight α)
      (degreePartitionWeight_nonneg α)).symm
  unfold cauchyPartitionCoefficient at hfactor
  simp_rw [hAlt] at hfactor
  apply mul_right_cancel₀ hD
  calc
    _ = D * PowerSeries.coeff d
        (∏ j : Fin (n + 1), PowerSeries.rescale (MvPolynomial.X j) H) := mul_comm _ _
    _ = _ := hfactor
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α _
      ring

end Langlands.GeneralLinear.Spherical
