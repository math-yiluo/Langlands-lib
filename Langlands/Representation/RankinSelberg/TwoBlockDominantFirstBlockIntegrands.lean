import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockMatrices
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence
import Langlands.Representation.RankinSelberg.UnramifiedTwistIntegrals
import Langlands.Representation.RankinSelberg.CharacterChange

/-! # Scalar and Jacobian bridges for the dominant first-block calculation -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent

open scoped NNReal

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance integrandBridgeTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance integrandBridgeValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance integrandBridgeLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance integrandBridgeSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance integrandBridgeMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance integrandBridgeBorel : BorelSpace F.Carrier := ⟨rfl⟩

theorem unequalRankIntegrandAt_mk {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ) (W : WhittakerFunctions ψ r)
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (X : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
    (v : GeneralLinear (n + 1) F.Carrier) :
    unequalRankIntegrandAt F j k hr ψ abv W W' s X (Quotient.mk _ v) =
      W.val (reindex (finCongr (congrArg (· + 1) hr.symm))
        (unequalRankMatrix j k v X)) * W'.val v *
          determinantWeight abv v (s - ((j + k + 1 : ℕ) : ℂ) / 2) := by
  subst r
  rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)

include h in
/-- The smaller JPSS rectangle contains the second block and all external rows. -/
theorem firstBlockSmallRank : t + (j + k + 1) = m 0 + (m 1 + 1 + j + k + 1) := by
  have := blockRanks_add h
  omega

variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))

/-- The representative scalar after moving the outer rectangle to the left.
Its determinant exponent includes the Jacobian of that first move. -/
def firstBlockUpperValue (s : ℂ) (g : GeneralLinear (t + 1) F.Carrier)
    (X : Matrix (Fin j) (Fin (t + 1)) F.Carrier) : ℂ :=
  scalarSection (fun i => (ell i).val) f g 1 *
    Wtest.val (rectangularUnipotent j k X * appendIdentity t (j + k + 1) g) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))

/-- The actual smaller JPSS integrand on the joined rows `Z,T`. -/
def firstBlockFiberIntegrand (s : ℂ)
    (v : GeneralLinear (m 0 + 1) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (T : Matrix (Fin j) (Fin (m 0 + 1)) F.Carrier) : ℂ :=
  unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (translateWhittaker ψ (t + (j + k + 1)) Wtest
      (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) g))
    (firstBlockCoefficient ell f g).val s (firstBlockRows j Z T) (Quotient.mk _ v)

theorem determinantWeight_firstBlockEmbedding (abv : AbsoluteValue F.Carrier ℝ)
    (v : GeneralLinear (m 0 + 1) F.Carrier) (s : ℂ) :
    determinantWeight abv (firstBlockEmbedding h F.Carrier v) s =
      determinantWeight abv v s := by
  change (abv (GeneralLinear.determinant (firstBlockEmbedding h F.Carrier v) : F.Carrier) : ℂ) ^ s = _
  rw [determinant_firstBlockEmbedding]
  rfl

theorem determinantWeight_lowerRadical (abv : AbsoluteValue F.Carrier ℝ)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) (s : ℂ) :
    determinantWeight abv (lowerRadical h F.Carrier Z) s = 1 := by
  change (abv (GeneralLinear.determinant (lowerRadical h F.Carrier Z) : F.Carrier) : ℂ) ^ s = 1
  simp only [determinant_lowerRadical, Units.val_one, map_one, Complex.ofReal_one,
    Complex.one_cpow]

/-- The exact supplied-Haar row Jacobian is the negative integral determinant weight. -/
theorem firstBlockRowJacobian (v : GeneralLinear (m 0 + 1) F.Carrier) :
    (((((F.canonicalTopologicalData.determinantNorm (m 0 + 1) v : ℝ≥0) ^ j)⁻¹ :
      ℝ≥0) : ℝ) : ℂ) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
        (-(j : ℂ)) := by
  simp only [determinantWeight, Complex.cpow_neg, Complex.cpow_natCast,
    NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, Complex.ofReal_pow]
  rfl

/-- Before the affine substitution, the upper value is the actual smaller
integrand times the external-row determinant power and the base-point weight. -/
theorem firstBlockUpperValue_fiber (s : ℂ)
    (v : GeneralLinear (m 0 + 1) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (U : Matrix (Fin j) (Fin (m 0 + 1)) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockUpperValue F h j k ell f Wtest s
        (firstBlockEmbedding h F.Carrier v * (lowerRadical h F.Carrier Z * g))
        (firstBlockColumns h j U Y) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (j : ℂ) *
        firstBlockFiberIntegrand F h j k ell f Wtest s v Z Y g (U * v.val + Y * Z) := by
  rw [firstBlockUpperValue, firstBlockFiberIntegrand, scalarSection_firstBlockEmbedding_mul,
    firstBlockCoefficient_lowerRadical_mul, inv_leviHalfModulus_blockPair_one,
    unequalRankIntegrandAt_mk, translateWhittaker_apply]
  have hm :
      rectangularUnipotent j k (firstBlockColumns h j U Y) *
          appendIdentity t (j + k + 1)
            (firstBlockEmbedding h F.Carrier v * (lowerRadical h F.Carrier Z * g)) =
        firstBlockSmallMatrix h j k v Z (U * v.val + Y * Z) *
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g) := by
    simp only [map_mul]
    rw [← mul_assoc, ← mul_assoc, firstBlock_matrix_factorization, mul_assoc]
  rw [hm]
  change _ = _ * _ *
    (Wtest.val (firstBlockSmallMatrix h j k v Z (U * v.val + Y * Z) * _) *
      _ * _)
  rw [determinantWeight_mul, determinantWeight_mul, determinantWeight_firstBlockEmbedding,
    determinantWeight_lowerRadical, one_mul]
  have hw :
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(((m 1 + 1 : ℕ) : ℂ) / 2)) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (j : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (s - ((m 1 + 1 + j + k + 1 : ℕ) : ℂ) / 2) := by
    rw [← determinantWeight_add, ← determinantWeight_add]
    congr 1
    push_cast
    ring
  calc
    _ = (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(((m 1 + 1 : ℕ) : ℂ) / 2)) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))) *
        (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
        Wtest.val (firstBlockSmallMatrix h j k v Z (U * v.val + Y * Z) *
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g)) *
        (firstBlockCoefficient ell f g).val.val v) := by ring
    _ = _ := by rw [hw]; ring

/-- The affine row substitution cancels the extra external-row determinant
weight, retaining the supplied scalar Haar and the base-point weight. -/
theorem integral_firstBlockUpperValue (ν : AdditiveHaarMeasure F.Carrier) (s : ℂ)
    (v : GeneralLinear (m 0 + 1) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    (∫ U, firstBlockUpperValue F h j k ell f Wtest s
      (firstBlockEmbedding h F.Carrier v * (lowerRadical h F.Carrier Z * g))
      (firstBlockColumns h j U Y) ∂rectangularMeasure ν j (m 0 + 1)) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      ∫ T, firstBlockFiberIntegrand F h j k ell f Wtest s v Z Y g T
        ∂rectangularMeasure ν j (m 0 + 1) := by
  simp_rw [firstBlockUpperValue_fiber]
  rw [integral_const_mul, integral_firstBlockRowChange]
  have hs (z : ℂ) :
      (((F.canonicalTopologicalData.determinantNorm (m 0 + 1) v : ℝ≥0) ^ j)⁻¹ :
        ℝ≥0) • z =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
        (-(j : ℂ)) * z := by
    rw [NNReal.smul_def, Complex.real_smul, firstBlockRowJacobian F j v]
  rw [hs]
  have hc :
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (j : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(j : ℂ)) = 1 := by
    rw [← determinantWeight_add]
    simp [determinantWeight]
  calc
    _ = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      ((determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (j : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(j : ℂ))) *
      ∫ T, firstBlockFiberIntegrand F h j k ell f Wtest s v Z Y g T
        ∂rectangularMeasure ν j (m 0 + 1)) := by ring
    _ = _ := by rw [hc, one_mul]

/-- Genuine absolute integrability is transported independently of the total
Bochner identity; both determinant factors are nonzero. -/
theorem integrable_firstBlockUpperValue_iff (ν : AdditiveHaarMeasure F.Carrier) (s : ℂ)
    (v : GeneralLinear (m 0 + 1) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Integrable (fun U => firstBlockUpperValue F h j k ell f Wtest s
      (firstBlockEmbedding h F.Carrier v * (lowerRadical h F.Carrier Z * g))
      (firstBlockColumns h j U Y)) (rectangularMeasure ν j (m 0 + 1)) ↔
      Integrable (firstBlockFiberIntegrand F h j k ell f Wtest s v Z Y g)
        (rectangularMeasure ν j (m 0 + 1)) := by
  simp_rw [firstBlockUpperValue_fiber]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (mul_ne_zero (determinantWeight_ne_zero _ _ _) (determinantWeight_ne_zero _ _ _)))]
  exact integrable_firstBlockRowChange_iff F ν v Z Y _

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
