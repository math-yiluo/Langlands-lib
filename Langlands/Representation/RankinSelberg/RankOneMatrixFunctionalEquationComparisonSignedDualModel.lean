import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockSigns
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport
import Langlands.Representation.RankinSelberg.DualModels

/-! # The actual same-character signed dual model and its block transport -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker
open AdjacentBlockReduction UnequalRankComplementaryConjugationProof

universe uF uV

section Algebraic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}

/-- The signed same-character dual, including the leading-coordinate right
translation needed to recover the Library's unsigned dual block. -/
def rankOneSignedDualFunction (n : ℕ)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  W (rankOneSignedWeyl n * inverseTranspose (n + 1) F g *
    rankOneWeylLeadingSign n)

@[simp] theorem inverseTranspose_rankOneSignedWeyl (n : ℕ) :
    inverseTranspose (n + 1) F (rankOneSignedWeyl n) =
      rankOneSignedWeyl n := by
  simp only [rankOneSignedWeyl, map_mul, inverseTranspose_weylLong,
    inverseTranspose_rankOneWeylAlternating]

/-- This is a genuine two-sided translate of the inverse-transpose function. -/
theorem rankOneSignedDualFunction_eq_iota
    (W : Langlands.GeneralLinear (n + 1) F → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    rankOneSignedDualFunction n W g =
      GodementJacquet.coefficientIota W
        (rankOneSignedWeyl n * g * rankOneWeylLeadingSign n) := by
  simp only [rankOneSignedDualFunction, GodementJacquet.coefficientIota,
    map_mul, inverseTranspose_rankOneSignedWeyl, inverseTranspose_rankOneWeylLeadingSign]

/-- The signed complementary argument becomes the actual unsigned dual
argument after the published alternating rectangular sign substitution. -/
theorem rankOneSignedDualFunction_block {m : ℕ}
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (g : Langlands.GeneralLinear 1 F) (X : Matrix (Fin m) (Fin 1) F) :
    rankOneSignedDualFunction (m + 1) W
        (blockMatrixAt m 0 (by omega) g X *
          rankOneSignedBlockWeyl (m + 1) (by omega)) =
      dualFunction (m + 1) W
        (blockMatrixAt m 0 (by omega) g (rankOneBlockSigns m X) *
          blockWeylAt 0 (m + 1) (by omega)) := by
  rw [rankOneSignedDualFunction, map_mul, inverseTranspose_rankOneSignedBlockWeyl,
    ← mul_assoc, rankOneSignedWeyl_iota_transport,
    alternating_blockMatrixAt_rankOne]
  simp only [dualFunction_apply, map_mul, blockWeylAt_eq,
    inverseTranspose_permutation, mul_assoc]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (ℓ : glFunctionals ψ n σ)

/-- Changing the inverse-character first dual back by the alternating diagonal
gives a genuine same-character functional on inverse-transpose pullback. -/
def rankOneSignedDualFunctional :
    glFunctionals ψ n (inverseTransposePullback σ) :=
  (characterChangeFunctionalEquiv ψ (inverseTransposePullback σ) (-1)).symm
    (firstDualFunctional ψ σ ℓ)

theorem rankOneSignedDualFunctional_apply (v : V) :
    (rankOneSignedDualFunctional ψ σ ℓ).val v =
      ℓ.val (σ (rankOneSignedWeyl n) v) := by
  change ℓ.val (σ (weylLong (n + 1) F)
      ((inverseTransposePullback σ) (characterChangeElement (-1 : Fˣ)⁻¹ n) v)) = _
  simp only [inv_neg, inv_one, inverseTransposePullback_apply,
    inverseTranspose_characterChangeElement_neg_one, ← Module.End.mul_apply,
    ← map_mul, rankOneSignedWeyl, rankOneWeylAlternating]

/-- The signed dual of each actual coefficient is an actual coefficient of
the same-character inverse-transpose model, with the explicit leading sign. -/
theorem rankOneSignedDualFunctional_coefficient (v : V)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (coefficientMap (inverseTransposePullback σ) (rankOneSignedDualFunctional ψ σ ℓ)
        (σ (rankOneWeylLeadingSign n) v)).val g =
      rankOneSignedDualFunction n (fun x => ℓ.val (σ x v)) g := by
  change (rankOneSignedDualFunctional ψ σ ℓ).val
      ((inverseTransposePullback σ) g (σ (rankOneWeylLeadingSign n) v)) = _
  rw [rankOneSignedDualFunctional_apply, inverseTransposePullback_apply,
    ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  rfl

/-- No model-equivalence hypothesis is needed to realize the signed dual of
an arbitrary vector in the original actual coefficient image. -/
theorem exists_rankOneSignedDualModel
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    ∃ wd : (glCoefficientModel ψ n (inverseTransposePullback σ)
        (rankOneSignedDualFunctional ψ σ ℓ)).toSubmodule,
      ∀ g, glModelFunction ψ n (inverseTransposePullback σ)
          (rankOneSignedDualFunctional ψ σ ℓ) wd g =
        rankOneSignedDualFunction n (glModelFunction ψ n σ ℓ w) g := by
  obtain ⟨v, hv⟩ := w.property
  refine ⟨modelMap (inverseTransposePullback σ) (rankOneSignedDualFunctional ψ σ ℓ)
    (σ (rankOneWeylLeadingSign n) v), fun g => ?_⟩
  have he := rankOneSignedDualFunctional_coefficient ψ σ ℓ v g
  change _ = rankOneSignedDualFunction n w.val.val g
  rw [← hv]
  exact he

end Algebraic

section BlockMeasure

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [LocallyCompactSpace F] [T2Space F]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
  (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure]
  (μ : Measure (Langlands.GeneralLinear 1 F)) [SFinite μ]

/-- Alternating signs in the complementary block preserve the actual product
measure, with the supplied additive Haar and no scalar factor. -/
theorem integral_rankOneSignedDualFunction_block (m : ℕ) (abv : AbsoluteValue F ℝ)
    (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F → ℂ) :
    (∫ z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F,
      determinantWeight abv z.1 s *
        rankOneSignedDualFunction (m + 1) W
          (blockMatrixAt m 0 (by omega) z.1 z.2 *
            rankOneSignedBlockWeyl (m + 1) (by omega))
      ∂μ.prod (rectangularMeasure ν m 1)) =
    ∫ z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F,
      determinantWeight abv z.1 s *
        dualFunction (m + 1) W
          (blockMatrixAt m 0 (by omega) z.1 z.2 *
            blockWeylAt 0 (m + 1) (by omega))
      ∂μ.prod (rectangularMeasure ν m 1) := by
  simp_rw [rankOneSignedDualFunction_block]
  exact ((MeasurePreserving.id μ).prod (rankOneBlockSigns_preserving ν m)).integral_comp
    ((MeasurableEquiv.refl (Langlands.GeneralLinear 1 F)).prodCongr
      (rankOneBlockSignsMeasurableEquiv m)).measurableEmbedding
    (fun z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F =>
      determinantWeight abv z.1 s *
        dualFunction (m + 1) W
          (blockMatrixAt m 0 (by omega) z.1 z.2 *
            blockWeylAt 0 (m + 1) (by omega)))

/-- The same substitution also preserves genuine absolute product convergence. -/
theorem integrable_rankOneSignedDualFunction_block_iff (m : ℕ)
    (abv : AbsoluteValue F ℝ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ) :
    Integrable
      (fun z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F =>
        determinantWeight abv z.1 s *
          rankOneSignedDualFunction (m + 1) W
            (blockMatrixAt m 0 (by omega) z.1 z.2 *
              rankOneSignedBlockWeyl (m + 1) (by omega)))
      (μ.prod (rectangularMeasure ν m 1)) ↔
    Integrable
      (fun z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F =>
        determinantWeight abv z.1 s *
          dualFunction (m + 1) W
            (blockMatrixAt m 0 (by omega) z.1 z.2 *
              blockWeylAt 0 (m + 1) (by omega)))
      (μ.prod (rectangularMeasure ν m 1)) := by
  simp_rw [rankOneSignedDualFunction_block]
  exact ((MeasurePreserving.id μ).prod (rankOneBlockSigns_preserving ν m)).integrable_comp_emb
    (g := fun z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F =>
      determinantWeight abv z.1 s *
        dualFunction (m + 1) W
          (blockMatrixAt m 0 (by omega) z.1 z.2 *
            blockWeylAt 0 (m + 1) (by omega)))
    ((MeasurableEquiv.refl (Langlands.GeneralLinear 1 F)).prodCongr
      (rankOneBlockSignsMeasurableEquiv m)).measurableEmbedding

end BlockMeasure

end Langlands.RankinSelberg
