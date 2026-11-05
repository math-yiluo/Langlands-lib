import Langlands.Representation.Plancherel.RationalFiniteChartModerateGrowthStatement
import Langlands.Representation.Exponents.RationalUnrestrictedLatticeBoundProof
import Langlands.Representation.Plancherel.RationalUniformizerCoordinateHeightProof
import Langlands.Representation.Plancherel.RationalCompactLatticePolynomialBoundProof
import Langlands.GroupScheme.Rational.PositiveCharacterOnIndependentCocharacters

/-! # Combining chartwise coefficient and coordinate-height bounds -/

noncomputable section

universe u uV uE uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation BruhatTits.SpecialCompact
open Aubert.General Aubert.General.RationalPointFamily

/-- Finite supplied independent weakly positive charts give the global
coefficientwise polynomial estimate. -/
theorem rationalFiniteChartModerateGrowth :
    RationalFiniteChartModerateGrowthStatement.{u, uV, uE, uI} := by
  intro F _ _ _ _ G hG S i hi
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro ν K0 hBasis E _ I _ _ gen hgen hnonneg S₁ S₂ T hS₁ hS₂ hT hcover
    n _ _ _ ρ hρ π hπ v φ
  classical
  have hbound : ∀ ε : E, ∃ (d : ℕ) (c : ℝ), 0 < c ∧
      ∀ (m : I → ℕ) (k₁ : rationalPoints G), k₁ ∈ S₁ →
        ∀ t : rationalPoints G, t ∈ T → ∀ k₂ : rationalPoints G, k₂ ∈ S₂ →
          ‖(φ : Module.Dual ℂ π) (π.representation
            (k₁ * uniformizerPowers i (.ofAdd (∑ a, m a • gen ε a)) * t * k₂) v)‖ ≤
              c * rationalMatrixNorm F ρ
                (k₁ * uniformizerPowers i (.ofAdd (∑ a, m a • gen ε a)) * t * k₂) ^ d := by
    intro ε
    obtain ⟨α, hα⟩ := positiveCharacterOnIndependentCocharacters
      F S hi.isSplitSubtorus.1 I (gen ε) (hgen ε)
    obtain ⟨D, A, hA, hheight⟩ := rationalUniformizerCoordinateHeight
      F G S i hi.isSplitSubtorus.2 n ρ hρ I (gen ε) α hα
    apply rationalCompactLatticePolynomialBound_of_power_height F G hG n ρ π I
      (fun m => uniformizerPowers i (.ofAdd (∑ a, m a • gen ε a)))
    · intro ψ w
      obtain ⟨a, ha, C, hC, hb⟩ := rationalUnrestrictedLatticeBound
        F G hG S i hi ν K0 hBasis π hπ I (gen ε) (hnonneg ε)
        {1} {1} {1} (isCompact_singleton) (isCompact_singleton)
        (Set.finite_singleton 1) ψ w
      exact ⟨a, ha, C, hC, fun m => by
        simpa only [one_mul, mul_one] using hb m 1 (by simp) 1 (by simp) 1 (by simp)⟩
    · refine ⟨(LocalField.residueCardinality F : ℝ), A, D, ?_, hA, ?_⟩
      · exact_mod_cast LocalField.residueCardinality_gt_one F
      · exact hheight
    · exact hS₁
    · exact hS₂
    · exact hT
  choose d c hc hb using hbound
  let D : ℕ := ∑ ε, d ε
  let C : ℝ := (∑ ε, c ε) + 1
  have hc0 : ∀ ε, 0 ≤ c ε := fun ε => (hc ε).le
  have hC : 0 < C := by
    dsimp [C]
    have hsum : 0 ≤ ∑ ε, c ε := Finset.sum_nonneg (fun ε _ => hc0 ε)
    linarith
  refine ⟨D, C, hC, fun g => ?_⟩
  obtain ⟨ε, m, k₁, hk₁, t, ht, k₂, hk₂, hg⟩ := hcover g
  have hd : d ε ≤ D :=
    Finset.single_le_sum (fun ε _ => Nat.zero_le (d ε)) (Finset.mem_univ ε)
  have hcC : c ε ≤ C := by
    dsimp [C]
    exact (Finset.single_le_sum (fun ε _ => hc0 ε) (Finset.mem_univ ε)).trans
      (le_add_of_nonneg_right zero_le_one)
  rw [hg]
  exact (hb ε m k₁ hk₁ t ht k₂ hk₂).trans
    (mul_le_mul hcC
      (pow_le_pow_right₀ (one_le_rationalMatrixNorm F ρ _) hd)
      (pow_nonneg (zero_le_one.trans (one_le_rationalMatrixNorm F ρ _)) _)
      hC.le)

end Langlands.Plancherel
