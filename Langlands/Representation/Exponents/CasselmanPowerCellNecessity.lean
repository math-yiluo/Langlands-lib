import Langlands.Representation.Exponents.NormalizedIwahoriEigenCoefficient
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Analysis.CountableCellLpProof
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Strict exponent bounds from supplied power-cell geometry

The cells are actual double cosets in the full central quotient. Their
disjointness and lower volumes are retained as geometric hypotheses.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace Langlands

universe uG uV uB

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of the actual double coset `K g^n K` in the full central
quotient. -/
def powerDoubleCosetCell (K : OpenSubgroup G) (g : G) (n : ℕ) :
    Set (G ⧸ Subgroup.center G) :=
  QuotientGroup.mk '' DoubleCoset.doubleCoset (g ^ n) K K

theorem isOpen_powerDoubleCosetCell (K : OpenSubgroup G) (g : G) (n : ℕ) :
    IsOpen (powerDoubleCosetCell K g n) := by
  apply QuotientGroup.isOpenMap_coe
  change IsOpen ((K : Set G) * {g ^ n} * (K : Set G))
  exact K.isOpen.mul_left

/-- Supplied pairwise disjointness and geometric lower volumes of the actual
power double cosets, measured relative to the image of `K`. -/
def HasGeometricPowerCellVolumes
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    (haar : Measure (G ⧸ Subgroup.center G)) (K : OpenSubgroup G)
    (g : G) (weight : ℝ≥0∞) : Prop :=
  Pairwise (fun m n => Disjoint (powerDoubleCosetCell K g m) (powerDoubleCosetCell K g n)) ∧
    ∀ n : ℕ, weight ^ n * haar (QuotientGroup.mk '' (K : Set G)) ≤
      haar (powerDoubleCosetCell K g n)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- L2 integrability of an exact eigen-coefficient forces its squared
eigenvalue times the supplied geometric volume weight to be below one. -/
theorem weighted_eigenvalue_lt_one_of_memLp_powerCells
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (haar : Measure (G ⧸ Subgroup.center G)) [haar.IsHaarMeasure]
    (ρ : Representation ℂ G V) (c : UnitaryCentralCharacter ρ)
    (K : OpenSubgroup G) (g : G) (weight : ℝ≥0∞)
    (hgeometry : HasGeometricPowerCellVolumes haar K g weight)
    (x : fixedVectors ρ K.toSubgroup) (ℓ : Module.Dual ℂ V)
    (hℓx : ℓ x ≠ 0) (hℓK : ∀ k ∈ K, ∀ y, ℓ (ρ k y) = ℓ y)
    (μ : ℂ) (hcoef : ∀ n : ℕ, ℓ (ρ (g ^ n) x) = μ ^ n * ℓ x)
    (hL2 : MemLp (c.coefficientNorm ℓ x) 2 haar) :
    weight * ‖μ‖ₑ ^ 2 < 1 := by
  have hcell : ∀ n a, a ∈ DoubleCoset.doubleCoset (g ^ n) K K →
      matrixCoefficient ρ ℓ x a = μ ^ n * ℓ x := by
    intro n a ha
    obtain ⟨u, hu, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.mp ha
    have hxk : ρ k (x : V) = x := x.property ⟨k, hk⟩
    change ℓ (ρ (u * g ^ n * k) x) = _
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hxk, hℓK u hu]
    exact hcoef n
  have hsum := countableCellLpLower (G ⧸ Subgroup.center G) ℕ haar
    (c.coefficientNorm ℓ x) 2 (by norm_num) (by norm_num) hL2
    (powerDoubleCosetCell K g)
    (fun n => (isOpen_powerDoubleCosetCell K g n).measurableSet)
    hgeometry.1 (fun n => ‖μ ^ n * ℓ x‖ₑ) (by
      rintro n q ⟨a, ha, rfl⟩
      rw [UnitaryCentralCharacter.coefficientNorm_mk, hcell n a ha, enorm_norm])
  let C : ℝ≥0∞ := ‖ℓ x‖ₑ ^ 2 * haar (QuotientGroup.mk '' (K : Set G))
  have hbase : 0 < haar (QuotientGroup.mk '' (K : Set G)) :=
    (QuotientGroup.isOpenMap_coe _ K.isOpen).measure_pos haar
      ⟨_, Set.mem_image_of_mem _ K.one_mem⟩
  have hC : C ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (enorm_ne_zero.mpr hℓx)) hbase.ne'
  have hterm : ∀ n : ℕ,
      (weight * ‖μ‖ₑ ^ 2) ^ n * C ≤
        ‖μ ^ n * ℓ x‖ₑ ^ (2 : ℝ≥0∞).toReal *
          haar (powerDoubleCosetCell K g n) := by
    intro n
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_mul, enorm_pow]
    calc
      _ = (‖μ‖ₑ ^ n * ‖ℓ x‖ₑ) ^ 2 *
          (weight ^ n * haar (QuotientGroup.mk '' (K : Set G))) := by
        dsimp [C]
        ring
      _ ≤ _ := by
        gcongr
        exact hgeometry.2 n
  have hfinite : (∑' n : ℕ, (weight * ‖μ‖ₑ ^ 2) ^ n * C) < ∞ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) hsum
  by_contra hnot
  have hge : 1 ≤ weight * ‖μ‖ₑ ^ 2 := le_of_not_gt hnot
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    tsub_eq_zero_iff_le.mpr hge, ENNReal.inv_zero, ENNReal.top_mul hC] at hfinite
  exact (lt_irrefl _) hfinite

end Langlands

namespace Langlands.Aubert.General

universe uG uV uB

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Square integrability forces a strict normalized exponent bound at a
central Levi point with the supplied cofinal contractions and actual
inverse-modulus power-cell lower geometry. -/
theorem norm_lt_one_of_normalizedJacquet_exponent_of_powerCells
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (haar : Measure (G ⧸ Subgroup.center G)) [haar.IsHaarMeasure]
    {B : Type uB} [Group B]
    (N M Nbar : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N)
    (π : SmoothRep.{0, uG, uV} ℂ G)
    (hsq : IsSquareIntegrableModCenter π.representation haar)
    (ι : B →* M) (χ : B →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter
      (((normalizedJacquetFunctor N M hN hMN).obj π).representation.comp ι) χ)
    (b : B) (hb : ι b ∈ Subgroup.center M)
    (hbasis : Jacquet.HasIwahoriContractionBasisAt N M Nbar ((ι b : M) : G))
    (hgeometry : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      HasGeometricPowerCellVolumes haar K ((ι b : M) : G)
        (‖(HaarModulus.closedInverseHalfCharacter N hN M hMN (ι b) : ℂ)‖ₑ ^ 2)) :
    ‖(χ b : ℂ)‖ < 1 := by
  obtain ⟨hπ, c, hL2⟩ := hsq
  obtain ⟨K, hK, x, ℓ, hℓx, hℓK, hℓn⟩ :=
    exists_eigen_coefficient_of_normalizedJacquet_generalizedEigencharacter
      N M Nbar hN hMN π hπ ι χ hχ b hb hbasis
  let η := HaarModulus.closedInverseHalfCharacter N hN M hMN (ι b)
  have hres := weighted_eigenvalue_lt_one_of_memLp_powerCells haar π.representation c
    K ((ι b : M) : G) (‖(η : ℂ)‖ₑ ^ 2) (hgeometry K hK)
    x (ℓ : Module.Dual ℂ π) hℓx hℓK
    ((η : ℂ)⁻¹ * (χ b : ℂ)) hℓn (hL2 ℓ x)
  have hcancel : ‖(η : ℂ)‖ₑ ^ 2 * ‖(η : ℂ)⁻¹ * (χ b : ℂ)‖ₑ ^ 2 =
      ‖(χ b : ℂ)‖ₑ ^ 2 := by
    rw [← mul_pow, ← enorm_mul, mul_inv_cancel_left₀ (Units.ne_zero _)]
  rw [hcancel] at hres
  have hnorm : ‖(χ b : ℂ)‖ₑ < 1 := by
    by_contra hnot
    exact (not_le_of_gt hres) (one_le_pow₀ (le_of_not_gt hnot))
  rw [← ofReal_norm] at hnorm
  exact ENNReal.ofReal_lt_one.mp hnorm

end Langlands.Aubert.General
