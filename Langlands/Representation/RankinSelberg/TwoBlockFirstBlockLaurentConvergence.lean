import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSlices
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.DualWhittakerType
import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

/-!
# Spectral series of the original and transformed small integrals

For representations of full Whittaker type and nonzero functionals, the actual
unequal-rank integral of every pair of coefficient-image vectors converges absolutely on
a right half-plane, by the published unequal-rank analytic theorem; there it is the
absolutely summable series of its determinant-slice coefficients. The transformed
integral is the same object for the inverse-transpose pair, the inverse additive
character and the exchanged blocks.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The slice coefficient at a fixed large rank, with the rank equality transporting
only types. -/
def unequalRankSliceCoefficientAt {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (μ : letI := F.canonicalTopologicalData.topology
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier)]
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
    (W : letI := F.canonicalTopologicalData.topology; WhittakerFunctions ψ r)
    (W' : letI := F.canonicalTopologicalData.topology; InverseWhittakerFunctions ψ n)
    (m : ℤ) : ℂ := by
  subst hr
  exact unequalRankSliceCoefficient F.canonicalTopologicalData j k ψ μ ν W W' m

/-- The actual small integral of coefficient-image vectors is, on a right half-plane, the
absolutely summable series of its slice coefficients. -/
theorem smallIntegral_series {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1)) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F.Carrier)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule),
            ∃ C : ℝ, ∀ s : ℂ, C < s.re →
              Summable (fun m : ℤ =>
                ‖unequalRankSliceCoefficientAt F j k hr ψ μ (rectangularMeasure ν j (n + 1))
                    f.val f'.val m * spectralPoint T.residueCardinality s ^ m‖) ∧
              HasSum (fun m : ℤ =>
                unequalRankSliceCoefficientAt F j k hr ψ μ (rectangularMeasure ν j (n + 1))
                    f.val f'.val m * spectralPoint T.residueCardinality s ^ m)
                (unequalRankIntegralAt j k hr ψ (normalizedAbsoluteValue T) μ
                  (rectangularMeasure ν j (n + 1)) f.val f'.val s) := by
  subst hr
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f'
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hconv, -, -, -⟩ :=
    unequalRankAnalytic.{uF, uV, uW} F T n j k ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨a, ha⟩ := hconv f f'
  exact ⟨a, fun s hs => unequalRank_sliceExpansion T j k ψ μ (rectangularMeasure ν j (n + 1))
    f.val f'.val s (ha s hs)⟩

/-- The actual transformed small integral is, on a right half-plane, the absolutely
summable series of the slice coefficients of the inverse-transpose pair. -/
theorem dualSmallIntegral_series {n r : ℕ} (hnr : n < r) (j k : ℕ)
    (hr : r = n + (j + k + 1)) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F.Carrier)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule),
            ∃ C : ℝ, ∀ s : ℂ, C < s.re →
              Summable (fun m : ℤ =>
                ‖unequalRankSliceCoefficientAt F k j (by omega) (ψ.scale (-1)) μ
                    (rectangularMeasure ν k (n + 1))
                    (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
                      (blockWeylAt n r hnr))
                    (secondDualFunction ψ n f'.val) m *
                  spectralPoint T.residueCardinality s ^ m‖) ∧
              HasSum (fun m : ℤ =>
                unequalRankSliceCoefficientAt F k j (by omega) (ψ.scale (-1)) μ
                    (rectangularMeasure ν k (n + 1))
                    (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
                      (blockWeylAt n r hnr))
                    (secondDualFunction ψ n f'.val) m *
                  spectralPoint T.residueCardinality s ^ m)
                (dualUnequalRankModelIntegralAt hnr j k hr ψ (normalizedAbsoluteValue T) μ ν
                  π σ ℓ ℓ' f f' s) := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f'
  have hπdual : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσdual : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ σ hσ
  exact smallIntegral_series F k j (by omega) (ψ.scale (-1)) μ hμ hμσ ν
    (inverseTransposePullback π) (inverseTransposePullback σ) hπdual hσdual
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
    (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f)
    (secondDualModelMap ψ σ ℓ' f')

/-- The unequal-rank integrand at a fixed large rank, with the rank equality transporting
only types. -/
def unequalRankIntegrandAt {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ)
    (W : letI := F.canonicalTopologicalData.topology; WhittakerFunctions ψ r)
    (W' : letI := F.canonicalTopologicalData.topology; InverseWhittakerFunctions ψ n)
    (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier) :
    LeftUnipotentQuotient n F.Carrier → ℂ := by
  letI := F.canonicalTopologicalData.topology
  subst hr
  exact unequalRankIntegrand ψ abv j k W W' s x

/-- On every determinant slice, the inner rectangular integral at `s = 0` of the actual
small integrand of coefficient-image vectors is integrable. -/
theorem smallIntegrand_integrableOn_slice {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1)) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F.Carrier)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
            (m : ℤ),
            Integrable (fun q => ∫ x, unequalRankIntegrandAt F j k hr ψ
                (normalizedAbsoluteValue T) f.val f'.val 0 x q ∂rectangularMeasure ν j (n + 1))
              (μ.restrict (determinantSlice T n m)) := by
  subst hr
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f' m
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hconv, -, -, -⟩ :=
    unequalRankAnalytic.{uF, uV, uW} F T n j k ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨a, ha⟩ := hconv f f'
  let s : ℂ := ((a + 1 : ℝ) : ℂ)
  have hs : a < s.re := by simp [s]
  have hG : Integrable (fun q => ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k
      f.val f'.val s x q ∂rectangularMeasure ν j (n + 1)) μ :=
    (ha s hs).integral_prod_left
  have hX : spectralPoint T.residueCardinality s ^ m ≠ 0 :=
    zpow_ne_zero _ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans T.residueCardinality_gt_one) s)
  refine ((hG.restrict).mul_const ((spectralPoint T.residueCardinality s ^ m)⁻¹)).congr ?_
  refine (ae_restrict_iff' (measurableSet_determinantSlice T n m)).mpr
    (Filter.Eventually.of_forall fun q hq => ?_)
  change (∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k f.val f'.val s x q
      ∂rectangularMeasure ν j (n + 1)) * (spectralPoint T.residueCardinality s ^ m)⁻¹ =
    ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k f.val f'.val 0 x q
      ∂rectangularMeasure ν j (n + 1)
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [unequalRankIntegrand_eq_mul_spectralPoint_zpow T j k ψ f.val f'.val s x m q hq,
    mul_assoc, mul_inv_cancel₀ hX, mul_one]

/-- On every determinant slice, the inner integral at `s = 0` of the actual transformed
small integrand is integrable. -/
theorem dualIntegrand_integrableOn_slice {n r : ℕ} (hnr : n < r) (j k : ℕ)
    (hr : r = n + (j + k + 1)) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F.Carrier)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
            (m : ℤ),
            Integrable (fun q => ∫ z, unequalRankIntegrandAt F k j (by omega) (ψ.scale (-1))
                (normalizedAbsoluteValue T)
                (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
                  (blockWeylAt n r hnr))
                (secondDualFunction ψ n f'.val) 0 z q ∂rectangularMeasure ν k (n + 1))
              (μ.restrict (determinantSlice T n m)) := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f' m
  have hπdual : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσdual : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ σ hσ
  exact smallIntegrand_integrableOn_slice F k j (by omega) (ψ.scale (-1)) μ hμ hμσ ν
    (inverseTransposePullback π) (inverseTransposePullback σ) hπdual hσdual
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
    (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f)
    (secondDualModelMap ψ σ ℓ' f') m

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
