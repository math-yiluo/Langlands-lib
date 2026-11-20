import Langlands.Automorphic.FiniteLevelConstantTermRestriction
import Langlands.Automorphic.CuspidalAdmissible.CuspIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Covariance of the adelic two-block constant term on the Levi -/

noncomputable section
universe u v

set_option autoImplicit false

namespace Langlands.GeneralLinear

variable {R : Type u} [CommRing R] {a b n : ℕ} (h : a + b = n)

private theorem blockDiagonalEmbedding_reindex_val (z : GeneralLinear a R × GeneralLinear b R) :
    ((reindex (R := R) (finSumFinEquiv.trans (finCongr h))).symm
      (blockDiagonalEmbedding h z)).val = Matrix.fromBlocks z.1.val 0 0 z.2.val := by
  ext i j
  change blockSum z
    ((finCongr h).symm ((finCongr h) (finSumFinEquiv i)))
    ((finCongr h).symm ((finCongr h) (finSumFinEquiv j))) = _
  simp only [Equiv.symm_apply_apply]
  rcases z with ⟨A, D⟩
  cases i <;> cases j <;> simp

/-- The block diagonal embedding commutes with change of coefficient ring. -/
theorem map_blockDiagonalEmbedding {S : Type v} [CommRing S] (f : R →+* S)
    (z : GeneralLinear a R × GeneralLinear b R) :
    Matrix.GeneralLinearGroup.map f (blockDiagonalEmbedding h z) =
      blockDiagonalEmbedding h (Matrix.GeneralLinearGroup.map f z.1,
        Matrix.GeneralLinearGroup.map f z.2) := by
  let e := finSumFinEquiv.trans (finCongr h)
  apply (reindex (R := S) e).symm.injective
  apply Units.ext
  have he (g : GeneralLinear n R) : ((reindex (R := S) e).symm
      (Matrix.GeneralLinearGroup.map f g)).val =
        (((reindex (R := R) e).symm g).val).map f := rfl
  rw [he, blockDiagonalEmbedding_reindex_val, blockDiagonalEmbedding_reindex_val,
    Matrix.fromBlocks_map, Matrix.map_zero f (map_zero f), Matrix.map_zero f (map_zero f)]
  rfl

/-- The block diagonal embedding is continuous in both matrices. -/
theorem continuous_blockDiagonalEmbedding [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (blockDiagonalEmbedding (R := R) h) :=
  (reindexContinuous (R := R) (finCongr h)).continuous.comp blockSumContinuous.continuous

/-- Commuting a block unipotent across a block diagonal changes its matrix coordinate. -/
theorem blockUnipotent_mul_blockDiagonalEmbedding (z : GeneralLinear a R × GeneralLinear b R)
    (X : Matrix (Fin a) (Fin b) R) :
    blockUnipotent h X * blockDiagonalEmbedding h z =
      blockDiagonalEmbedding h z * blockUnipotent h (z.1⁻¹.val * X * z.2.val) := by
  let e := reindex (R := R) (finSumFinEquiv.trans (finCongr h))
  have hu (Y : Matrix (Fin a) (Fin b) R) :
      e.symm (blockUnipotent h Y) = sumBlockUnipotent Y := by
    change e.symm (e (sumBlockUnipotent Y)) = _
    exact e.symm_apply_apply _
  apply e.symm.injective
  rw [map_mul, map_mul, hu, hu]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockDiagonalEmbedding_reindex_val]
  change Matrix.fromBlocks 1 X 0 1 * Matrix.fromBlocks z.1.val 0 0 z.2.val =
    Matrix.fromBlocks z.1.val 0 0 z.2.val *
      Matrix.fromBlocks 1 (z.1⁻¹.val * X * z.2.val) 0 1
  have hX : z.1.val * (z.1⁻¹.val * X * z.2.val) = X * z.2.val := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, zero_add, add_zero, hX]

end Langlands.GeneralLinear

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear MeasureTheory ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "AdelicMatrix" => Matrix (Fin a) (Fin b) (Adeles F)
local notation "QuotientMatrix" => Matrix (Fin a) (Fin b) (AdeleQuotient F)
local notation "RationalLevi" => RationalGL F a × RationalGL F b

private def rationalLeviMatrixChange (z : RationalLevi) (X : AdelicMatrix) : AdelicMatrix :=
  (AdelicGL.rational F a z.1)⁻¹.val * X * (AdelicGL.rational F b z.2).val

private theorem rationalLeviMatrixChange_add (z : RationalLevi) (X Y : AdelicMatrix) :
    rationalLeviMatrixChange F z (X + Y) =
      rationalLeviMatrixChange F z X + rationalLeviMatrixChange F z Y := by
  simp only [rationalLeviMatrixChange, Matrix.mul_add, Matrix.add_mul]

private theorem rationalLeviMatrixChange_inv (z : RationalLevi) (X : AdelicMatrix) :
    rationalLeviMatrixChange F z⁻¹ (rationalLeviMatrixChange F z X) = X := by
  unfold rationalLeviMatrixChange
  simp only [Prod.fst_inv, Prod.snd_inv, map_inv, inv_inv]
  rw [← Matrix.mul_assoc (AdelicGL.rational F a z.1).val,
    ← Matrix.mul_assoc (AdelicGL.rational F a z.1).val,
    Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

private theorem rationalLeviMatrixChange_principal (z : RationalLevi)
    (C : Matrix (Fin a) (Fin b) F) :
    rationalLeviMatrixChange F z (C.map (diagonal F)) =
      (z.1⁻¹.val * C * z.2.val).map (diagonal F) := by
  simp only [Matrix.map_mul]
  rfl

private def rationalLeviQuotientChangeFun (z : RationalLevi) (X : QuotientMatrix) :
    QuotientMatrix :=
  matrixQuotientMap (rationalLeviMatrixChange F z (matrixLift X))

private theorem rationalLeviQuotientChangeFun_mk (z : RationalLevi) (X : AdelicMatrix) :
    rationalLeviQuotientChangeFun F z (matrixQuotientMap X) =
      matrixQuotientMap (rationalLeviMatrixChange F z X) := by
  obtain ⟨C, hC⟩ :=
    exists_rational_of_matrixQuotientMap_eq (matrixQuotientMap_matrixLift (matrixQuotientMap X)).symm
  unfold rationalLeviQuotientChangeFun
  rw [hC, rationalLeviMatrixChange_add, rationalLeviMatrixChange_principal,
    GeneralLinearBlockUnipotent.matrixQuotientMap_rational_add]

private theorem continuous_rationalLeviQuotientChangeFun (z : RationalLevi) :
    Continuous (rationalLeviQuotientChangeFun F z) := by
  let q := isOpenQuotientMap_matrixQuotientMap (K := F) a b
  rw [← q.continuous_comp_iff]
  simp_rw [Function.comp_def, rationalLeviQuotientChangeFun_mk]
  apply q.continuous.comp
  unfold rationalLeviMatrixChange
  fun_prop

/-- The coordinate change from commuting a rational Levi element induces an additive
homeomorphism on the compact block-unipotent quotient. -/
def rationalLeviQuotientChange (z : RationalLevi) : QuotientMatrix ≃ₜ+ QuotientMatrix where
  toFun := rationalLeviQuotientChangeFun F z
  invFun := rationalLeviQuotientChangeFun F z⁻¹
  left_inv X := by
    rw [← matrixQuotientMap_matrixLift X, rationalLeviQuotientChangeFun_mk,
      rationalLeviQuotientChangeFun_mk, rationalLeviMatrixChange_inv]
  right_inv X := by
    rw [← matrixQuotientMap_matrixLift X, rationalLeviQuotientChangeFun_mk,
      rationalLeviQuotientChangeFun_mk]
    simpa only [inv_inv] using congrArg matrixQuotientMap
      (rationalLeviMatrixChange_inv F z⁻¹ (matrixLift X))
  map_add' X Y := by
    rw [← matrixQuotientMap_matrixLift X, ← matrixQuotientMap_matrixLift Y,
      ← GeneralLinearBlockUnipotent.matrixQuotientMap_add, rationalLeviQuotientChangeFun_mk,
      rationalLeviMatrixChange_add, GeneralLinearBlockUnipotent.matrixQuotientMap_add,
      rationalLeviQuotientChangeFun_mk, rationalLeviQuotientChangeFun_mk]
  continuous_toFun := continuous_rationalLeviQuotientChangeFun F z
  continuous_invFun := continuous_rationalLeviQuotientChangeFun F z⁻¹

local instance : MeasurableSpace QuotientMatrix := borel _
local instance : BorelSpace QuotientMatrix := ⟨rfl⟩

variable [CompactSpace (AdeleQuotient F)]

/-- A rational block diagonal change of coordinates preserves normalized Haar. -/
theorem map_rationalLeviQuotientChange (z : RationalLevi) :
    Measure.map (rationalLeviQuotientChange F z) (matrixQuotientHaar F a b) =
      matrixQuotientHaar F a b := by
  let := matrixQuotientHaar_isAddHaarMeasure F a b
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The left action of the rational block diagonal group preserves the constant term. -/
theorem constantTerm_rational_blockDiagonalEmbedding
    (f : ContinuousRationalFunctions F n) (z : RationalLevi) (g : AdelicGL F n) :
    constantTerm F n h f (AdelicGL.rational F n (blockDiagonalEmbedding h z) * g) =
      constantTerm F n h f g := by
  have hmove (X : AdelicMatrix) :
      blockUnipotent h X * AdelicGL.rational F n (blockDiagonalEmbedding h z) =
        AdelicGL.rational F n (blockDiagonalEmbedding h z) *
          blockUnipotent h (rationalLeviMatrixChange F z X) := by
    change blockUnipotent h X * Matrix.GeneralLinearGroup.map (diagonal F)
        (blockDiagonalEmbedding h z) =
      Matrix.GeneralLinearGroup.map (diagonal F) (blockDiagonalEmbedding h z) *
        blockUnipotent h (rationalLeviMatrixChange F z X)
    rw [map_blockDiagonalEmbedding]
    exact blockUnipotent_mul_blockDiagonalEmbedding h
      (AdelicGL.rational F a z.1, AdelicGL.rational F b z.2) X
  have hcomp (X : QuotientMatrix) :
      constantTermIntegrand F n h f (AdelicGL.rational F n (blockDiagonalEmbedding h z) * g) X =
        constantTermIntegrand F n h f g (rationalLeviQuotientChange F z X) := by
    obtain ⟨X, rfl⟩ := (isOpenQuotientMap_matrixQuotientMap (K := F) a b).surjective X
    change _ = constantTermIntegrand F n h f g
      (rationalLeviQuotientChangeFun F z (matrixQuotientMap X))
    rw [rationalLeviQuotientChangeFun_mk, constantTermIntegrand_mk, constantTermIntegrand_mk,
      ← mul_assoc, hmove, mul_assoc, evaluate_rational]
  simp only [constantTerm, hcomp]
  have hint := integral_map_equiv (μ := matrixQuotientHaar F a b)
    (rationalLeviQuotientChange F z).toHomeomorph.toMeasurableEquiv
    (constantTermIntegrand F n h f g)
  rw [show Measure.map (rationalLeviQuotientChange F z).toHomeomorph.toMeasurableEquiv
      (matrixQuotientHaar F a b) = matrixQuotientHaar F a b from
    map_rationalLeviQuotientChange F z] at hint
  exact hint.symm

/-- Integrating the jointly continuous compact-quotient integrand gives a continuous
function on the adelic group. -/
theorem continuous_blockConstantTerm (f : ContinuousRationalFunctions F n) :
    Continuous (constantTerm F n h f) := by
  let μ := matrixQuotientHaar F a b
  let : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (matrixQuotientHaar F a b))
  let integrand : C(AdelicGL F n, C(QuotientMatrix, ℂ)) :=
    ContinuousMap.curry ⟨_, (continuous_constantTermIntegrand_uncurry F n h f).comp continuous_swap⟩
  let toL1 : C(QuotientMatrix, ℂ) →L[ℝ] Lp ℂ 1 μ := ContinuousMap.toLp 1 μ ℝ
  have he (g : AdelicGL F n) :
      (∫ X, toL1 (integrand g) X ∂μ) = constantTerm F n h f g :=
    integral_congr_ae (ContinuousMap.coeFn_toLp μ (integrand g))
  rw [← funext he]
  exact continuous_integral.comp (toL1.continuous.comp integrand.continuous)

end Langlands.Automorphic
