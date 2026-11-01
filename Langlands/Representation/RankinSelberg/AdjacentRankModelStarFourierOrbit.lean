import Langlands.Representation.RankinSelberg.AdjacentRankModelStarFourierCovariance
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.HarmonicAnalysis.RowFourierMeasure
import Langlands.Group.GL.Mirabolic

/-! Row changes of variables for the fixed-character model-star identity. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Matrix
open scoped NNReal

universe uF

section Algebra

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {n : ℕ}

/-- Pullback of a rectangular test by left multiplication on its rows. -/
def adjacentRankRowTranslate (h : GeneralLinear n K) :
    SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) :=
  rectangularLeftRightTranslate h 1

@[simp] theorem adjacentRankRowTranslate_apply (h : GeneralLinear n K)
    (φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    adjacentRankRowTranslate h φ m = φ (h.val * m) := by
  simp [adjacentRankRowTranslate]

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- Left multiplication acts on both blocks of the last-column splitting. -/
theorem adjacentRank_mul_join (a : Matrix (Fin n) (Fin n) K)
    (x : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    a * rectangularJoin x y = rectangularJoin (a * x) (a *ᵥ y) := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp [Matrix.mul_apply]

/-- Left row pullback commutes with the right Schwartz action. -/
theorem adjacentRankRowTranslate_right (h : GeneralLinear n K)
    (a : GeneralLinear (n + 1) K)
    (φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    adjacentRankRowTranslate h (rectangularTranslate a φ) =
      rectangularTranslate a (adjacentRankRowTranslate h φ) := by
  ext m
  simp only [adjacentRankRowTranslate_apply, rectangularTranslate_apply, Matrix.mul_assoc]

end Algebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelStarOrbitFourierTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance modelStarOrbitFourierValuative : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance modelStarOrbitFourierLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance modelStarOrbitFourierT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance modelStarOrbitFourierSecondCountable : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
local instance modelStarOrbitFourierMeasurable : MeasurableSpace F.Carrier := borel _
local instance modelStarOrbitFourierBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance modelStarOrbitFourierDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hself : IsSelfDual ψ ν) {n : ℕ}

private theorem partialIntegral_row (φ : Matrix (Fin n) (Fin (n + 1)) F.Carrier → ℂ)
    (x : Matrix (Fin n) (Fin n) F.Carrier) (y : Fin n → F.Carrier) :
    partialFourierIntegral ψ ν φ (rectangularJoin x y) =
      rowFourierIntegral (ψ.scale (-1)) ν n (fun u => φ (rectangularJoin x u)) y := by
  unfold partialFourierIntegral rowFourierIntegral
  simp only [rectangularFirstColumns_join, rectangularLastColumn_join]
  congr 1
  funext u
  change φ (rectangularJoin x u) * ψ.complex (-rowPairing y u) =
    ψ.complex ((↑(-1 : F.Carrierˣ) : F.Carrier) * rowPairing u y) * φ (rectangularJoin x u)
  simp only [Units.val_neg, Units.val_one, neg_one_mul]
  have hp : rowPairing u y = rowPairing y u := by
    simp only [rowPairing, mul_comm]
  rw [hp, mul_comm]

/-- The inverse-character partial Fourier transform under a left row change. -/
theorem adjacentRank_partialFourier_rowTranslate
    (h : GeneralLinear n F.Carrier)
    (φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) F.Carrier))
    (x : Matrix (Fin n) (Fin n) F.Carrier) (y : Fin n → F.Carrier) :
    partialFourierEquiv ψ ν n hself (adjacentRankRowTranslate h φ) (rectangularJoin x y) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-1) *
        partialFourierEquiv ψ ν n hself φ
          (rectangularJoin (h.val * x) ((inverseTranspose n F.Carrier h).val *ᵥ y)) := by
  let : SigmaFinite ν.measure := selfDualSigmaFinite F.Carrier ψ ν hself
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      ν.measure.map (fun z => a * z) =
        (F.canonicalTopologicalData.normalizedAbsHom a)⁻¹ • ν.measure :=
    padicScalarHaarScaling F F.canonicalTopologicalData ν.measure (Units.mk0 a ha)
  have hf (u : Fin n → F.Carrier) :
      adjacentRankRowTranslate h φ (rectangularJoin x u) =
        φ (rectangularJoin (h.val * x) (u ᵥ* (inverseTranspose n F.Carrier h⁻¹).val)) := by
    simp only [adjacentRankRowTranslate_apply, adjacentRank_mul_join,
      inverseTranspose_coe, inv_inv, vecMul_transpose]
  simp only [partialFourierEquiv_apply, partialIntegral_row]
  simp_rw [hf]
  have he := rowFourierIntegral_vecMul F.canonicalTopologicalData.normalizedAbsHom
    (ψ.scale (-1)) ν hχ (inverseTranspose n F.Carrier h⁻¹)
    (fun u => φ (rectangularJoin (h.val * x) u)) y
  have hdet : Matrix.det (inverseTranspose n F.Carrier h⁻¹).val = Matrix.det h.val := by
    rw [inverseTranspose_coe, inv_inv, Matrix.det_transpose]
  have hi : ((inverseTranspose n F.Carrier h⁻¹)⁻¹).val.transpose = (h⁻¹).val := by
    rw [← map_inv, inv_inv, inverseTranspose_coe, Matrix.transpose_transpose]
  rw [hdet, hi] at he
  simpa only [mulVec_transpose, inverseTranspose_coe, determinantWeight,
    Complex.cpow_neg_one, PadicField.TopologicalData.normalizedAbsHom_coe,
    normalizedAbsoluteValue_apply] using he

/-- The full plus Fourier transform under a left row change. -/
theorem adjacentRank_fullFourier_rowTranslate
    (h : GeneralLinear n F.Carrier)
    (φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) F.Carrier))
    (m : Matrix (Fin n) (Fin (n + 1)) F.Carrier) :
    rectangularFourierEquiv ψ ν n (n + 1) hself (adjacentRankRowTranslate h φ) m =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-((n + 1 : ℕ) : ℂ)) *
        rectangularFourierEquiv ψ ν n (n + 1) hself φ
          ((inverseTranspose n F.Carrier h).val * m) := by
  let T := F.canonicalTopologicalData
  let c : ℝ≥0 := ((T.determinantNorm n h : ℝ≥0) ^ (n + 1))⁻¹
  have hm : (rectangularMeasure ν n (n + 1)).map (rectangularLeftRightHomeomorph h 1) =
      c • rectangularMeasure ν n (n + 1) := by
    change (rectangularMeasure ν n (n + 1)).map (fun X => h.val * X * (1 : GeneralLinear (n + 1) F.Carrier).val) =
      c • rectangularMeasure ν n (n + 1)
    simpa only [c, inv_one, Units.val_one, map_one, one_pow, div_one] using
      padicRectangularHaarScaling F T n (n + 1) (rectangularMeasure ν n (n + 1)) h 1
  have he := rectangularFourierIntegral_leftRight ψ ν h 1 c hm φ m
  have hc : ((c : ℝ) : ℂ) =
      determinantWeight (normalizedAbsoluteValue T) h (-((n + 1 : ℕ) : ℂ)) := by
    simp only [c, NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, Complex.ofReal_pow,
      T.determinantNorm_coe, determinantWeight, Complex.cpow_neg, Complex.cpow_natCast]
    rfl
  rw [rectangularFourierEquiv_apply]
  have hfun : ((adjacentRankRowTranslate h φ :
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) F.Carrier)) :
      Matrix (Fin n) (Fin (n + 1)) F.Carrier → ℂ) = fun Y => φ (h.val * Y) := by
    funext Y
    exact adjacentRankRowTranslate_apply h φ Y
  rw [hfun]
  simpa only [map_one, Units.val_one, Matrix.mul_one, hc,
    rectangularFourierEquiv_apply] using he


private theorem orbit_determinant_inverseTranspose (h : GeneralLinear n F.Carrier) :
    determinant (inverseTranspose n F.Carrier h) = (determinant h)⁻¹ := by
  apply Units.ext
  change Matrix.det (h⁻¹ : GeneralLinear n F.Carrier).val.transpose =
    Matrix.det (h⁻¹ : GeneralLinear n F.Carrier).val
  exact Matrix.det_transpose _

private theorem orbit_weight_inverseTranspose (h : GeneralLinear n F.Carrier) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (inverseTranspose n F.Carrier h) s =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-s) := by
  unfold determinantWeight
  change (((normalizedAbsoluteValue F.canonicalTopologicalData)
    (determinant (inverseTranspose n F.Carrier h) : F.Carrier) : ℝ) : ℂ) ^ s = _
  rw [orbit_determinant_inverseTranspose, Units.val_inv_eq_inv_val, map_inv₀,
    Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  · rfl
  · rw [Complex.arg_ofReal_of_nonneg
      ((normalizedAbsoluteValue F.canonicalTopologicalData).nonneg _)]
    exact Real.pi_ne_zero.symm

private theorem orbit_weight_add (h : GeneralLinear n F.Carrier) (s t : ℂ) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (s + t) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h s *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    ((normalizedAbsoluteValue F.canonicalTopologicalData).ne_zero h.det_ne_zero))

variable {r : ℕ}

/-- The inverse transpose of an upper unipotent matrix fixes the last basis column. -/
theorem adjacentRank_inverseTranspose_unipotent_epsilon
    (u : upperUnipotent (r + 1) F.Carrier) :
    (inverseTranspose (r + 1) F.Carrier u.val).val *ᵥ adjacentRankEpsilon F.Carrier r =
      adjacentRankEpsilon F.Carrier r := by
  ext i
  rw [inverseTranspose_mulVec_adjacentRankEpsilon]
  have hm := upperUnipotent_le_mirabolic (u⁻¹).property i
  simpa only [adjacentRankEpsilon, Pi.single_apply, Subgroup.coe_inv, eq_comm] using hm

/-- The kernel on a right upper-unipotent orbit has a constant last column. -/
theorem adjacentRank_kernel_right_unipotent (h : GeneralLinear (r + 1) F.Carrier)
    (u : upperUnipotent (r + 1) F.Carrier) :
    adjacentRankKernelMatrix (h * u.val) =
      rectangularJoin (h.val * u.val.val)
        ((inverseTranspose (r + 1) F.Carrier h).val *ᵥ adjacentRankEpsilon F.Carrier r) := by
  simp only [adjacentRankKernelMatrix, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    adjacentRank_inverseTranspose_unipotent_epsilon]

/-- Evaluation of the original fixed-character action along a right unipotent orbit. -/
theorem adjacentRank_rho0_kernel_right_orbit
    (h : GeneralLinear (r + 1) F.Carrier)
    (u : upperUnipotent (r + 1) F.Carrier) (a : GeneralLinear (r + 2) F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    rectangularRho0 ψ ν (r + 1) hself a Φ (adjacentRankKernelMatrix (h * u.val)) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h 1 *
        partialFourierEquiv ψ ν (r + 1) hself
          (rectangularTranslate a (adjacentRankRowTranslate h
            ((partialFourierEquiv ψ ν (r + 1) hself).symm Φ)))
          (rectangularJoin u.val.val (adjacentRankEpsilon F.Carrier r)) := by
  let φ := (partialFourierEquiv ψ ν (r + 1) hself).symm Φ
  have he := adjacentRank_partialFourier_rowTranslate F ψ ν hself h
    (rectangularTranslate a φ) u.val.val (adjacentRankEpsilon F.Carrier r)
  rw [adjacentRankRowTranslate_right] at he
  have hc : determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h 1 *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-1) = 1 := by
    rw [← orbit_weight_add]
    simp [determinantWeight]
  rw [he, ← mul_assoc, hc, one_mul]
  rw [rectangularRho0_apply, adjacentRank_kernel_right_unipotent]

/-- The reflected orbit kernel is the split matrix produced by both Fourier row changes. -/
theorem adjacentRank_kernel_reflected_right_orbit
    (h : GeneralLinear (r + 1) F.Carrier)
    (u : upperUnipotent (r + 1) F.Carrier) :
    adjacentRankKernelMatrix
        ((inverseTranspose (r + 1) F.Carrier h * weylLong (r + 1) F.Carrier) * u.val) =
      rectangularJoin
        ((inverseTranspose (r + 1) F.Carrier h).val *
          ((weylLong (r + 1) F.Carrier).val * u.val.val))
        (h.val *ᵥ ((weylLong (r + 1) F.Carrier).val *ᵥ adjacentRankEpsilon F.Carrier r)) := by
  rw [adjacentRank_kernel_right_unipotent]
  simp only [map_mul, inverseTranspose_involutive, inverseTranspose_weylLong,
    Units.val_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]

/-- The full Fourier transform of the row-translated partial test on the reflected orbit. -/
theorem adjacentRank_fullFourier_kernel_reflected_orbit
    (h : GeneralLinear (r + 1) F.Carrier)
    (u : upperUnipotent (r + 1) F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
        (partialFourierEquiv ψ ν (r + 1) hself
          (adjacentRankRowTranslate h ((partialFourierEquiv ψ ν (r + 1) hself).symm Φ)))
        (rectangularJoin ((weylLong (r + 1) F.Carrier).val * u.val.val)
          ((weylLong (r + 1) F.Carrier).val *ᵥ adjacentRankEpsilon F.Carrier r)) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-((r + 1 : ℕ) : ℂ)) *
        rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ
          (adjacentRankKernelMatrix
            ((inverseTranspose (r + 1) F.Carrier h * weylLong (r + 1) F.Carrier) * u.val)) := by
  let φ := (partialFourierEquiv ψ ν (r + 1) hself).symm Φ
  let H := rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
  let T := partialFourierEquiv ψ ν (r + 1) hself
  have hH : H (adjacentRankRowTranslate h φ) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-((r + 2 : ℕ) : ℂ)) •
        adjacentRankRowTranslate (inverseTranspose (r + 1) F.Carrier h) (H φ) := by
    ext m
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      adjacentRankRowTranslate_apply]
    exact adjacentRank_fullFourier_rowTranslate F ψ ν hself h φ m
  have hT : T (H φ) = H Φ := by
    rw [← rectangularFourierCommutation ψ ν (r + 1) hself φ]
    simp only [φ, partialFourierEquiv_apply_symm_apply]
    rfl
  have hc : determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-((r + 2 : ℕ) : ℂ)) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (inverseTranspose (r + 1) F.Carrier h) (-1) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h (-((r + 1 : ℕ) : ℂ)) := by
    rw [orbit_weight_inverseTranspose, neg_neg, ← orbit_weight_add]
    congr 1
    push_cast
    ring
  change H (T (adjacentRankRowTranslate h φ)) _ = _
  rw [rectangularFourierCommutation ψ ν (r + 1) hself, hH, map_smul]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [adjacentRank_partialFourier_rowTranslate F ψ ν hself, hT,
    inverseTranspose_involutive, ← mul_assoc, hc, adjacentRank_kernel_reflected_right_orbit]

end Langlands.RankinSelberg
