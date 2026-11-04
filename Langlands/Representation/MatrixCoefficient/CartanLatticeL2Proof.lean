import Langlands.Representation.MatrixCoefficient.CartanLatticeL2Statement
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Langlands.Analysis.FiniteLatticeCellL2Proof

/-! # L2 assembly from finite translated lattice cells -/

namespace Langlands

open MeasureTheory
open scoped BigOperators ENNReal

theorem cartanLatticeL2.{uG, uV, uI} :
    CartanLatticeL2Statement.{uG, uV, uI} := by
  intro G V _ _ _ _ _ I _ τ w hw K T hT hcover ρ hρ c _ _ μ _ hvol hcoeff
  classical
  obtain ⟨D, hD, hvol⟩ := hvol
  let qcell : (I → ℕ) → G → Set (G ⧸ Subgroup.center G) := fun n t =>
    (QuotientGroup.mk : G → G ⧸ Subgroup.center G) ''
      DoubleCoset.doubleCoset (τ n * t) K K
  let cell : (I → ℕ) → Set (G ⧸ Subgroup.center G) :=
    fun n => ⋃ t ∈ T, qcell n t
  have hcovers : (⋃ n, cell n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨n, k₁, hk₁, t, ht, k₂, hk₂, z, hz, rfl⟩ := hcover g
      apply Set.mem_iUnion.mpr
      refine ⟨n, Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, ?_⟩⟩⟩
      refine ⟨k₁ * τ n * t * k₂, ?_, ?_⟩
      · exact DoubleCoset.mem_doubleCoset.mpr
          ⟨k₁, hk₁, k₂, hk₂, by simp only [mul_assoc]⟩
      · change (QuotientGroup.mk (k₁ * τ n * t * k₂) :
          G ⧸ Subgroup.center G) = QuotientGroup.mk (k₁ * τ n * t * k₂ * z)
        simp only [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
  have hvols (n : I → ℕ) :
      μ (cell n) ≤ ENNReal.ofReal
        (((hT.toFinset.card : ℝ) * D) * ∏ i, w i ^ n i) := by
    calc
      _ ≤ ∑ t ∈ hT.toFinset, μ (qcell n t) := by
        simpa only [Set.Finite.mem_toFinset] using
          (measure_biUnion_finset_le (μ := μ) hT.toFinset (qcell n))
      _ ≤ ∑ _t ∈ hT.toFinset, ENNReal.ofReal (D * ∏ i, w i ^ n i) :=
        Finset.sum_le_sum fun t ht => hvol n t (hT.mem_toFinset.mp ht)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
  refine ⟨hρ, c, ?_⟩
  intro φ v
  obtain ⟨a, ha, C, hC, hbound⟩ := hcoeff φ v
  apply finiteLatticeCellL2 (G ⧸ Subgroup.center G) I μ
    (c.coefficientNorm φ v) (c.aestronglyMeasurable_coefficientNorm φ v (hρ.1 v) μ)
    cell hcovers C ((hT.toFinset.card : ℝ) * D) hC
    (mul_nonneg (Nat.cast_nonneg _) hD) a w
    (fun i => (ha i).1) hw (fun i => (ha i).2) 0
  · intro n q hq
    obtain ⟨t, hq⟩ := Set.mem_iUnion.mp hq
    obtain ⟨ht, g, hg, rfl⟩ := Set.mem_iUnion.mp hq
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    rw [c.coefficientNorm_mk, norm_norm]
    simp only [pow_zero, mul_one]
    change ‖(φ : Module.Dual ℂ V) (ρ (k₁ * (τ n * t) * k₂) v)‖ ≤
      C * ∏ i, a i ^ n i
    simpa only [mul_assoc] using
      hbound n k₁ hk₁ t ht k₂ hk₂
  · exact hvols

end Langlands
