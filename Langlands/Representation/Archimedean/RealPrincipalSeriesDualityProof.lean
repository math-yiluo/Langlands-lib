import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientReduction
import Langlands.Representation.Archimedean.RealStandardModuleFourier
import Langlands.LinearAlgebra.TriangularUnitary
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator
open MeasureTheory
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealPrincipalSeriesDuality

set_option backward.isDefEq.respectTransparency false

/-! ## The normalized Haar measure on `O(n)` -/

/-- The Borel σ-algebra on `O(n)`. -/
@[reducible] def measurableSpaceK (n : ℕ) : MeasurableSpace (unitaryCompact ℝ n) := borel _

attribute [local instance] measurableSpaceK

local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-- The orthogonal matrices form a compact set of matrices. -/
theorem isCompact_unitaryGroup_set (n : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  apply (isCompact_closedBall (0 : ℝ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU i j
  exact mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hU i j)

/-- `O(n)` is compact. -/
instance compactSpace_unitaryCompact (n : ℕ) : CompactSpace (unitaryCompact ℝ n) := by
  have : CompactSpace (Matrix.unitaryGroup (Fin n) ℝ) :=
    isCompact_iff_compactSpace.mp (isCompact_unitaryGroup_set n)
  let φ : Matrix.unitaryGroup (Fin n) ℝ → unitaryCompact ℝ n :=
    fun U => ⟨Unitary.toUnits U, U.2⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
    exact continuous_star.comp continuous_subtype_val
  refine Function.Surjective.compactSpace hφ ?_
  rintro ⟨g, hg⟩
  refine ⟨⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rfl

/-- The normalized Haar measure on `O(n)`. -/
def haarK (n : ℕ) : Measure (unitaryCompact ℝ n) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance isHaarMeasure_haarK (n : ℕ) : (haarK n).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance isProbabilityMeasure_haarK (n : ℕ) : IsProbabilityMeasure (haarK n) :=
  ⟨Measure.haarMeasure_self⟩

/-- The Haar measure of the compact group `O(n)` is also right invariant. -/
instance isMulRightInvariant_haarK (n : ℕ) : (haarK n).IsMulRightInvariant := by
  constructor
  intro g
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (Measure.map (· * g) (haarK n)) (haarK n)
  have huniv := congrArg (fun μ : Measure (unitaryCompact ℝ n) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply] at huniv
  have hc : Measure.haarScalarFactor (Measure.map (· * g) (haarK n)) (haarK n) = 1 := by
    have : ((Measure.haarScalarFactor (Measure.map (· * g) (haarK n)) (haarK n) : NNReal) :
        ENNReal) = 1 := by
      rw [huniv]
      simp
    exact_mod_cast this
  rw [h, hc, one_smul]

/-- A continuous function on `O(n)` is integrable. -/
theorem integrable_of_continuous {n : ℕ} {F : unitaryCompact ℝ n → ℂ} (hF : Continuous F) :
    Integrable F (haarK n) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)


/-! ## Integrals of left derivatives vanish -/

/-- If `γ` is a one-parameter subgroup of `O(n)` and `D(k)` is the derivative at `0` of
`t ↦ Ψ(γ(t) k)` for continuous `Ψ` and `D`, then `∫_{O(n)} D = 0`: by left invariance the
function `t ↦ ∫ Ψ(γ(t) k) dk` is constant, and its derivative is `∫ D` by differentiation
under the integral sign. -/
theorem integral_eq_zero_of_hasDerivAt_left {n : ℕ} (γ : ℝ → unitaryCompact ℝ n)
    (hγ : ∀ s t, γ (s + t) = γ s * γ t)
    {Ψ D : unitaryCompact ℝ n → ℂ} (hΨ : Continuous Ψ) (hD : Continuous D)
    (hderiv : ∀ k, HasDerivAt (fun t => Ψ (γ t * k)) (D k) 0) :
    ∫ k, D k ∂haarK n = 0 := by
  have h0 : γ 0 = 1 := by
    have h := hγ 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hall : ∀ k t, HasDerivAt (fun s => Ψ (γ s * k)) (D (γ t * k)) t := by
    intro k t
    have h := hderiv (γ t * k)
    rw [← sub_self t] at h
    have h' := h.comp_sub_const t t
    refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    change Ψ (γ s * k) = Ψ (γ (s - t) * (γ t * k))
    rw [← mul_assoc, ← hγ, sub_add_cancel]
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hD.continuousOn
  have hcont : ∀ t, Continuous fun k : unitaryCompact ℝ n => Ψ (γ t * k) :=
    fun t => hΨ.comp (continuous_const.mul continuous_id)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := haarK n)
    (F := fun t k => Ψ (γ t * k)) (F' := fun t k => D (γ t * k)) (x₀ := 0)
    (bound := fun _ => C) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont t).aestronglyMeasurable)
    (integrable_of_continuous (hcont 0))
    ((hD.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun k t _ => hC _ (Set.mem_univ _))
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ => hall k t)
  have hconst : (fun t => ∫ k, Ψ (γ t * k) ∂haarK n) = fun _ => ∫ k, Ψ k ∂haarK n := by
    funext t
    exact integral_mul_left_eq_self Ψ (γ t)
  have hd := key.2
  rw [hconst] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (∫ k, Ψ k ∂haarK n))
  simpa [h0] using hz


/-! ## Matrix calculus -/

section MatrixCalculus

variable {n : ℕ}

/-- The entries of a differentiable matrix-valued curve are differentiable. -/
theorem hasDerivAt_entry {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {M' : Matrix (Fin n) (Fin n) ℝ}
    {t : ℝ} (h : HasDerivAt M M' t) (i j : Fin n) :
    HasDerivAt (fun s => M s i j) (M' i j) t := by
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact L.hasFDerivAt.comp_hasDerivAt t h

/-- The derivative of `t ↦ exp(t A)` at `0` is `A`. -/
theorem hasDerivAt_exp_smul_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  simpa using h

/-- The inclusion of `O(n)` into the matrices is continuous. -/
theorem continuous_unitaryCompact_val :
    Continuous fun k : unitaryCompact ℝ n =>
      ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
  Units.continuous_val.comp continuous_subtype_val

end MatrixCalculus

/-! ## Upper triangular directions -/

section Upper

variable {n : ℕ}

/-- The exponents `n - 1 - 2i` of the modulus character of the upper triangular Borel
subgroup. -/
def modulusExponent (n : ℕ) (i : Fin n) : ℂ := (n : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)

/-- `φ` transforms on the left by the modulus character of the upper triangular Borel
subgroup, evaluated on positive diagonal matrices `exp(diag x)`. -/
def IsModulusEquivariant (φ : Langlands.GeneralLinear n ℝ → ℂ) : Prop :=
  ∀ (x : Fin n → ℝ) (u : Langlands.GeneralLinear.upperUnipotent n ℝ) (g : Langlands.GeneralLinear n ℝ),
    φ (matrixExpUnit n (Matrix.diagonal x) * (u : Langlands.GeneralLinear n ℝ) * g) =
      Complex.exp (∑ i, modulusExponent n i * (x i : ℂ)) * φ g

/-- `1 + t N` is upper triangular for upper triangular `N`. -/
theorem isUpperTriangular_one_add_smul {N : Matrix (Fin n) (Fin n) ℝ}
    (hN : N.IsUpperTriangular) (t : ℝ) : (1 + t • N).IsUpperTriangular := by
  intro i j hij
  have hne : i ≠ j := fun h => (lt_irrefl j) (h ▸ hij)
  simp [Matrix.one_apply_ne hne, hN hij]

/-- `1 + t N` for a strictly upper triangular `N`, as an upper unipotent element. -/
def unipotentLine (N : Matrix (Fin n) (Fin n) ℝ) (hN : N.IsUpperTriangular)
    (hd : ∀ i, N i i = 0) (t : ℝ) : Langlands.GeneralLinear.upperUnipotent n ℝ :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + t • N) (by
    rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_one_add_smul hN t)]
    simp [hd]),
   ⟨isUpperTriangular_one_add_smul hN t, fun i => by
      change (1 + t • N) i i = 1
      simp [hd]⟩⟩

theorem unipotentLine_val (N : Matrix (Fin n) (Fin n) ℝ) (hN : N.IsUpperTriangular)
    (hd : ∀ i, N i i = 0) (t : ℝ) :
    (((unipotentLine N hN hd t : Langlands.GeneralLinear.upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = 1 + t • N :=
  rfl

/-- The derivative of a modulus-equivariant function in an upper triangular direction:
`dφ_k(U k) = (∑ᵢ (n - 1 - 2i) Uᵢᵢ) φ(k)`, computed along the curve `exp(t diag U)(1 + t N) k`
with `N` the strictly upper part of `U`. -/
theorem fderiv_upperTriangular {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (hmod : IsModulusEquivariant φ)
    (k : Langlands.GeneralLinear n ℝ) {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsUpperTriangular) :
    fderiv ℝ (unitsExtension φ) (k : Matrix (Fin n) (Fin n) ℝ)
        (U * (k : Matrix (Fin n) (Fin n) ℝ)) =
      (∑ i, modulusExponent n i * (U i i : ℂ)) * φ k := by
  set Δ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i => U i i with hΔ
  set N : Matrix (Fin n) (Fin n) ℝ := U - Δ with hN
  have hNu : N.IsUpperTriangular := hU.sub (Matrix.blockTriangular_diagonal _)
  have hNd : ∀ i, N i i = 0 := fun i => by simp [hN, hΔ]
  set Γ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t =>
    NormedSpace.exp (t • Δ) * (1 + t • N) * (k : Matrix (Fin n) (Fin n) ℝ) with hΓ
  have hΓd : HasDerivAt Γ (U * (k : Matrix (Fin n) (Fin n) ℝ)) 0 := by
    have h1 := hasDerivAt_exp_smul_zero Δ
    have h2 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + t • N) N 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add 1
    have h3 := (h1.mul h2).mul_const (k : Matrix (Fin n) (Fin n) ℝ)
    have e : (Δ * (1 + (0 : ℝ) • N) + NormedSpace.exp ((0 : ℝ) • Δ) * N) *
        (k : Matrix (Fin n) (Fin n) ℝ) = U * (k : Matrix (Fin n) (Fin n) ℝ) := by
      simp only [zero_smul, add_zero, NormedSpace.exp_zero, one_mul, mul_one]
      rw [hN, add_sub_cancel]
    exact h3.congr_deriv e
  have hΓ0 : Γ 0 = k := by simp [hΓ]
  have hval : ∀ t : ℝ, Γ t = ((matrixExpUnit n (Matrix.diagonal fun i => t * U i i) *
      ((unipotentLine N hNu hNd t : Langlands.GeneralLinear.upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) * k :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
    intro t
    have hsd : t • Δ = Matrix.diagonal fun i => t * U i i := by
      rw [hΔ, ← Matrix.diagonal_smul]
      rfl
    simp only [Units.val_mul, matrixExpUnit_val, unipotentLine_val, hΓ, hsd]
  have hcomp : (fun t => unitsExtension φ (Γ t)) = fun t : ℝ =>
      Complex.exp (∑ i, modulusExponent n i * ((t * U i i : ℝ) : ℂ)) * φ k := by
    funext t
    rw [hval t, unitsExtension_val, hmod]
  have hd1 : HasDerivAt (fun t => unitsExtension φ (Γ t))
      (fderiv ℝ (unitsExtension φ) (k : Matrix (Fin n) (Fin n) ℝ)
        (U * (k : Matrix (Fin n) (Fin n) ℝ))) 0 := by
    have hdiff : HasFDerivAt (unitsExtension φ)
        (fderiv ℝ (unitsExtension φ) (k : Matrix (Fin n) (Fin n) ℝ)) (Γ 0) := by
      rw [hΓ0]
      exact (differentiableAt_unitsExtension hφ (Units.isUnit k)).hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hΓd
  have hlin : HasDerivAt (fun t : ℝ => ∑ i, modulusExponent n i * ((t * U i i : ℝ) : ℂ))
      (∑ i, modulusExponent n i * (U i i : ℂ)) 0 := by
    have e : (fun t : ℝ => ∑ i, modulusExponent n i * ((t * U i i : ℝ) : ℂ)) =
        fun t : ℝ => (t : ℂ) * ∑ i, modulusExponent n i * (U i i : ℂ) := by
      funext t
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [e]
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const
      (∑ i, modulusExponent n i * (U i i : ℂ))
  have hd2 : HasDerivAt (fun t : ℝ =>
      Complex.exp (∑ i, modulusExponent n i * ((t * U i i : ℝ) : ℂ)) * φ k)
      ((∑ i, modulusExponent n i * (U i i : ℂ)) * φ k) 0 := by
    have := hlin.cexp.mul_const (φ k)
    simpa using this
  rw [hcomp] at hd1
  exact hd1.unique hd2

end Upper

/-! ## Rotation directions -/

section Rotation

variable {n : ℕ}

/-- The generator `E_{ba} - E_{ab}` of the rotations in the coordinates `a, b`. -/
def rotGen (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single b a 1 - Matrix.single a b 1

theorem rotGen_transpose (a b : Fin n) : (rotGen a b)ᵀ = -rotGen a b := by
  simp [rotGen, Matrix.transpose_sub, Matrix.transpose_single]

theorem rotGen_mem_skewAdjoint (a b : Fin n) :
    rotGen a b ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ) := by
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, rotGen_transpose]

/-- The one-parameter subgroup `t ↦ exp(t W)` of `O(n)` for an antisymmetric `W`. -/
def expK (W : Matrix (Fin n) (Fin n) ℝ) (hW : W ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ))
    (t : ℝ) : unitaryCompact ℝ n :=
  ⟨matrixExpUnit n (t • W),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hW)⟩

theorem expK_val (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : W ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ)) (t : ℝ) :
    (((expK W hW t : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = NormedSpace.exp (t • W) :=
  rfl

theorem expK_add (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : W ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ)) (s t : ℝ) :
    expK W hW (s + t) = expK W hW s * expK W hW t :=
  Subtype.ext (matrixExpUnit_add_smul n W s t)

/-- The matrix `m X mᵀ`. -/
def conjT (X m : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := m * X * mᵀ

theorem continuous_conjT (X : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun m : Matrix (Fin n) (Fin n) ℝ => conjT X m := by
  unfold conjT
  fun_prop

/-- The derivative of `t ↦ exp(tW) m X (exp(tW) m)ᵀ` at `0`, for an antisymmetric `W`. -/
theorem hasDerivAt_conjT_exp (X W m : Matrix (Fin n) (Fin n) ℝ) (hW : Wᵀ = -W) :
    HasDerivAt (fun t : ℝ => conjT X (NormedSpace.exp (t • W) * m))
      (W * conjT X m - conjT X m * W) 0 := by
  have e : (fun t : ℝ => conjT X (NormedSpace.exp (t • W) * m)) =
      fun t : ℝ => NormedSpace.exp (t • W) * conjT X m * NormedSpace.exp (t • Wᵀ) := by
    funext t
    simp only [conjT, Matrix.transpose_mul, mul_assoc]
    rw [← Matrix.exp_transpose, Matrix.transpose_smul]
  rw [e]
  have h1 := hasDerivAt_exp_smul_zero W
  have h2 := hasDerivAt_exp_smul_zero Wᵀ
  have h3 := (h1.mul_const (conjT X m)).mul h2
  refine h3.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, mul_one, one_mul, hW, mul_neg]
  abel

theorem rotGen_comm_apply (S : Matrix (Fin n) (Fin n) ℝ) {a b : Fin n} (hab : a ≠ b) :
    (rotGen a b * S - S * rotGen a b) b a = S a a - S b b := by
  simp only [rotGen, Matrix.sub_apply, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ hab.symm,
    Matrix.mul_single_apply_of_ne _ _ _ _ _ hab]
  ring

/-- The derivative along a rotation of `k ↦ (k X kᵀ)_{ba} φ(k)`. -/
theorem hasDerivAt_rotation {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (X W : Matrix (Fin n) (Fin n) ℝ)
    (hW : W ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ)) (hWt : Wᵀ = -W)
    (a b : Fin n) (k : unitaryCompact ℝ n) :
    HasDerivAt (fun t : ℝ =>
        ((conjT X (((expK W hW t * k : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ) b a : ℝ) : ℂ) *
        φ ((expK W hW t * k : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ))
      ((((W * conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) -
          conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * W) b a :
          ℝ) : ℂ) * φ k +
        ((conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) b a : ℝ) :
          ℂ) *
        fderiv ℝ (unitsExtension φ) ((k : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ)
          (W * ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))) 0 := by
  set km : Matrix (Fin n) (Fin n) ℝ := ((k : Langlands.GeneralLinear n ℝ) :
    Matrix (Fin n) (Fin n) ℝ) with hkm
  have hval : ∀ t : ℝ, (((expK W hW t * k : unitaryCompact ℝ n) :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
        NormedSpace.exp (t • W) * km := fun t => rfl
  have hA : HasDerivAt (fun t : ℝ =>
      ((conjT X (NormedSpace.exp (t • W) * km) b a : ℝ) : ℂ))
      (((W * conjT X km - conjT X km * W) b a : ℝ) : ℂ) 0 :=
    (hasDerivAt_entry (hasDerivAt_conjT_exp X W km hWt) b a).ofReal_comp
  have hcurve : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • W) * km) (W * km) 0 :=
    (hasDerivAt_exp_smul_zero W).mul_const km
  have hψ : HasFDerivAt (unitsExtension φ) (fderiv ℝ (unitsExtension φ) km)
      (NormedSpace.exp ((0 : ℝ) • W) * km) := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]
    exact (differentiableAt_unitsExtension hφ (Units.isUnit _)).hasFDerivAt
  have hB : HasDerivAt (fun t : ℝ => unitsExtension φ (NormedSpace.exp (t • W) * km))
      (fderiv ℝ (unitsExtension φ) km (W * km)) 0 := by
    have h := hψ.comp_hasDerivAt (0 : ℝ) hcurve
    exact h
  have hAB := hA.mul hB
  have hφ0 : unitsExtension φ (NormedSpace.exp ((0 : ℝ) • W) * km) = φ k := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul, hkm, unitsExtension_val]
  have hc0 : conjT X (NormedSpace.exp ((0 : ℝ) • W) * km) = conjT X km := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]
  rw [hφ0, hc0] at hAB
  refine hAB.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change _ = ((conjT X (NormedSpace.exp (t • W) * km) b a : ℝ) : ℂ) *
    unitsExtension φ (NormedSpace.exp (t • W) * km)
  rw [← hval t, unitsExtension_val]

end Rotation

/-! ## Integrals of right derivatives of modulus-equivariant functions vanish -/

section ModulusIntegral

variable {n : ℕ}

/-- `∑ᵢ (n - 1 - 2i) xᵢ = ∑_{a < b} (x_a - x_b)`. -/
theorem sum_modulusExponent (x : Fin n → ℝ) :
    ∑ i, modulusExponent n i * (x i : ℂ) =
      ∑ a, ∑ b, if a < b then ((x a - x b : ℝ) : ℂ) else 0 := by
  have h1 : ∀ a : Fin n, (∑ b, if a < b then (x a : ℂ) else 0) =
      ((n - 1 - (a : ℕ) : ℕ) : ℂ) * x a := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi,
      nsmul_eq_mul]
  have h2 : ∀ b : Fin n, (∑ a, if a < b then (x b : ℂ) else 0) = ((b : ℕ) : ℂ) * x b := by
    intro b
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio,
      nsmul_eq_mul]
  have h3 : (∑ a : Fin n, ∑ b : Fin n, if a < b then ((x a - x b : ℝ) : ℂ) else 0) =
      (∑ a : Fin n, ∑ b : Fin n, if a < b then (x a : ℂ) else 0) -
        ∑ b : Fin n, ∑ a : Fin n, if a < b then (x b : ℂ) else 0 := by
    rw [Finset.sum_comm (f := fun b a => if a < b then (x b : ℂ) else 0),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> push_cast <;> ring
  rw [h3, Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_congr rfl fun b _ => h2 b,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have hc : ((n - 1 - (i : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - ((i : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  rw [hc, modulusExponent]
  ring

/-- `∑_{a < b} S_{ba} (E_{ba} - E_{ab})` as the difference of its lower and upper parts. -/
theorem rotSum_eq (S : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, if a < b then S b a • rotGen a b else 0) =
      Matrix.of (fun i j => if j < i then S i j else 0) -
        Matrix.of (fun i j => if i < j then S j i else 0) := by
  have e1 : ∀ a b : Fin n, (if a < b then S b a • rotGen a b else 0) =
      Matrix.single b a (if a < b then S b a else 0) -
        Matrix.single a b (if a < b then S b a else 0) := by
    intro a b
    split_ifs
    · simp [rotGen, smul_sub]
    · simp
  simp only [e1, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    conv_rhs => rw [Matrix.matrix_eq_sum_single (Matrix.of fun i j => if j < i then S i j else 0)]
    rfl
  · conv_rhs => rw [Matrix.matrix_eq_sum_single (Matrix.of fun i j => if i < j then S j i else 0)]
    rfl

/-- The entries of `∑_{a < b} S_{ba} (E_{ba} - E_{ab})`. -/
theorem rotSum_apply (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ a, ∑ b, if a < b then S b a • rotGen a b else 0) i j =
      (if j < i then S i j else 0) - (if i < j then S j i else 0) := by
  rw [rotSum_eq]
  rfl

/-- `S - ∑_{a < b} S_{ba} (E_{ba} - E_{ab})` is upper triangular with the diagonal of `S`. -/
theorem isUpperTriangular_sub_rotSum (S : Matrix (Fin n) (Fin n) ℝ) :
    (S - ∑ a, ∑ b, if a < b then S b a • rotGen a b else 0).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  rw [Matrix.sub_apply, rotSum_apply]
  simp [hij, lt_asymm hij]

theorem sub_rotSum_apply_self (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (S - ∑ a, ∑ b, if a < b then S b a • rotGen a b else 0) i i = S i i := by
  rw [Matrix.sub_apply, rotSum_apply]
  simp

/-- `kᵀ k = 1` for `k ∈ O(n)`. -/
theorem transpose_mul_self_of_mem (k : unitaryCompact ℝ n) :
    (((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))ᵀ *
      ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h := (mem_unitaryCompact_iff ℝ n (k : Langlands.GeneralLinear n ℝ)).mp k.2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The integrand attached to the rotations in the coordinates `a, b`:
`(W S - S W)_{ba} φ(k) + S_{ba} dφ_k(W k)` with `S = k X kᵀ` and `W = E_{ba} - E_{ab}`. -/
def rotationTerm (φ : Langlands.GeneralLinear n ℝ → ℂ) (X : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n) (k : unitaryCompact ℝ n) : ℂ :=
  (((rotGen a b * conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) -
      conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * rotGen a b) b a :
      ℝ) : ℂ) * φ k +
    ((conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) b a : ℝ) : ℂ) *
      fderiv ℝ (unitsExtension φ) ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)
        (rotGen a b * ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))

/-- Pointwise: on `O(n)`, the right derivative of a modulus-equivariant function is the sum of
the rotation terms over the pairs `a < b`. -/
theorem rightDerivative_eq_sum_rotationTerm {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (hmod : IsModulusEquivariant φ)
    (X : Matrix (Fin n) (Fin n) ℝ) (k : unitaryCompact ℝ n) :
    rightDerivative (matrixModel ℝ n) X φ (k : Langlands.GeneralLinear n ℝ) =
      ∑ a, ∑ b, if a < b then rotationTerm φ X a b k else 0 := by
  set km : Matrix (Fin n) (Fin n) ℝ := ((k : Langlands.GeneralLinear n ℝ) :
    Matrix (Fin n) (Fin n) ℝ) with hkm
  set S := conjT X km with hS
  set L := fderiv ℝ (unitsExtension φ) km with hL
  set R : Matrix (Fin n) (Fin n) ℝ := ∑ a, ∑ b, if a < b then S b a • rotGen a b else 0
    with hR
  have h1 : rightDerivative (matrixModel ℝ n) X φ (k : Langlands.GeneralLinear n ℝ) =
      L (km * X) := rightDerivative_eq_fderiv hφ X _
  have h2 : km * X = (S - R) * km + R * km := by
    rw [sub_mul, sub_add_cancel, hS, conjT, mul_assoc, transpose_mul_self_of_mem k, mul_one]
  have hU : L ((S - R) * km) = (∑ i, modulusExponent n i * (S i i : ℂ)) * φ k := by
    have h := fderiv_upperTriangular hφ hmod (k : Langlands.GeneralLinear n ℝ)
      (isUpperTriangular_sub_rotSum S)
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_rotSum_apply_self]
  have hRk : R * km = ∑ a, ∑ b, if a < b then S b a • (rotGen a b * km) else 0 := by
    rw [hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [smul_mul_assoc]
    · rw [zero_mul]
  have hLR : L (R * km) = ∑ a, ∑ b, if a < b then (S b a : ℂ) * L (rotGen a b * km) else 0 := by
    rw [hRk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [map_smul, Complex.real_smul]
    · rw [map_zero]
  have hterm : ∀ a b : Fin n, (if a < b then rotationTerm φ X a b k else 0) =
      (if a < b then ((S a a - S b b : ℝ) : ℂ) else 0) * φ k +
        (if a < b then (S b a : ℂ) * L (rotGen a b * km) else 0) := by
    intro a b
    split_ifs with hab
    · rw [rotationTerm, ← hkm, ← hS, ← hL, rotGen_comm_apply S (ne_of_lt hab)]
    · simp
  rw [h1, h2, map_add, hU, hLR, sum_modulusExponent, Finset.sum_mul]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_mul]

/-- The fderiv of the extension of a smooth function, along `O(n)`, is continuous. -/
theorem continuous_fderiv_unitsExtension {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) :
    Continuous fun k : unitaryCompact ℝ n =>
      fderiv ℝ (unitsExtension φ) ((k : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) := by
  have h := (contDiffOn_unitsExtension hφ).continuousOn_fderiv_of_isOpen
    isOpen_setOf_isUnit_matrix (by simp)
  exact h.comp_continuous continuous_unitaryCompact_val fun k => Units.isUnit _

theorem continuous_comp_val {φ : Langlands.GeneralLinear n ℝ → ℂ} (hφ : Continuous φ) :
    Continuous fun k : unitaryCompact ℝ n => φ (k : Langlands.GeneralLinear n ℝ) :=
  hφ.comp continuous_subtype_val

theorem continuous_rotationTerm {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (X : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n) : Continuous (rotationTerm φ X a b) := by
  have hS := (continuous_conjT X).comp (continuous_unitaryCompact_val (n := n))
  have hSe : ∀ i j : Fin n, Continuous fun k : unitaryCompact ℝ n =>
      ((conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i j : ℝ) : ℂ) :=
    fun i j => Complex.continuous_ofReal.comp
      ((continuous_apply j).comp ((continuous_apply i).comp hS))
  have hC : Continuous fun k : unitaryCompact ℝ n =>
      (((rotGen a b * conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) -
        conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * rotGen a b) b a :
        ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ((continuous_apply a).comp ((continuous_apply b).comp ?_))
    exact (continuous_const.mul hS).sub (hS.mul continuous_const)
  have hD : Continuous fun k : unitaryCompact ℝ n =>
      fderiv ℝ (unitsExtension φ) ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)
        (rotGen a b * ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) :=
    (continuous_fderiv_unitsExtension hφ).clm_apply
      (continuous_const.mul continuous_unitaryCompact_val)
  exact (hC.mul (continuous_comp_val hφ.continuous)).add ((hSe b a).mul hD)

theorem integral_rotationTerm {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (X : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n) : ∫ k, rotationTerm φ X a b k ∂haarK n = 0 := by
  have hS := (continuous_conjT X).comp (continuous_unitaryCompact_val (n := n))
  refine integral_eq_zero_of_hasDerivAt_left (expK (rotGen a b) (rotGen_mem_skewAdjoint a b))
    (expK_add _ _)
    (Ψ := fun k => ((conjT X ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) b a :
      ℝ) : ℂ) * φ k) ?_ (continuous_rotationTerm hφ X a b) ?_
  · exact (Complex.continuous_ofReal.comp ((continuous_apply a).comp
      ((continuous_apply b).comp hS))).mul (continuous_comp_val hφ.continuous)
  · intro k
    exact hasDerivAt_rotation hφ X (rotGen a b) (rotGen_mem_skewAdjoint a b)
      (rotGen_transpose a b) a b k

/-- The integral over `O(n)` of the right derivative of a smooth modulus-equivariant function
vanishes. -/
theorem integral_rightDerivative_eq_zero {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (hmod : IsModulusEquivariant φ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    ∫ k, rightDerivative (matrixModel ℝ n) X φ (k : Langlands.GeneralLinear n ℝ) ∂haarK n =
      0 := by
  have hc : ∀ a b : Fin n, Continuous fun k : unitaryCompact ℝ n =>
      if a < b then rotationTerm φ X a b k else 0 :=
    fun a b => continuous_if_const _ (fun _ => continuous_rotationTerm hφ X a b)
      (fun _ => continuous_const)
  simp_rw [rightDerivative_eq_sum_rotationTerm hφ hmod X]
  rw [integral_finsetSum _ fun a _ => integrable_of_continuous
    (continuous_finsetSum _ fun b _ => hc a b)]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_of_continuous (hc a b)]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : a < b
  · simp only [hab, ↓reduceIte]
    exact integral_rotationTerm hφ X a b
  · simp [hab]

end ModulusIntegral

/-! ## Products of principal series functions -/

section Products

variable {n : ℕ}

/-- Products of smooth functions on `GL_n(ℝ)` are smooth. -/
theorem contMDiff_mul_fun {f h : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (hh : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ h) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ fun g => f g * h g :=
  contMDiff_of_contDiffOn ((contDiffOn_unitsExtension hf).mul (contDiffOn_unitsExtension hh))
    fun g => by rw [unitsExtension_val, unitsExtension_val]

/-- The product rule for right derivatives. -/
theorem rightDerivative_mul_fun {f h : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (hh : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ h) (X : Matrix (Fin n) (Fin n) ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    rightDerivative (matrixModel ℝ n) X (fun g => f g * h g) g =
      rightDerivative (matrixModel ℝ n) X f g * h g +
        f g * rightDerivative (matrixModel ℝ n) X h g := by
  have h1 := hasDerivAt_mul_matrixExpUnit_smul (hf.of_le (mod_cast le_top)) g X
  have h2 := hasDerivAt_mul_matrixExpUnit_smul (hh.of_le (mod_cast le_top)) g X
  have h3 := hasDerivAt_mul_matrixExpUnit_smul
    ((contMDiff_mul_fun hf hh).of_le (mod_cast le_top)) g X
  have h0 : g * matrixExpUnit n ((0 : ℝ) • X) = g := by
    rw [zero_smul, matrixExpUnit_zero, mul_one]
  have h4 := h1.mul h2
  rw [h0] at h4
  exact h3.unique h4

theorem ofReal_exp_cpow (x : ℝ) (w : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp (x * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

/-- The positive diagonal matrix `exp(diag x)` as a diagonal unit. -/
theorem matrixExpUnit_diagonal (x : Fin n → ℝ) :
    matrixExpUnit n (Matrix.diagonal x) =
      (Langlands.GeneralLinear.Iwasawa.diagonalUnits
        (fun i => Units.mk0 (Real.exp (x i)) (Real.exp_pos _).ne') :
          Langlands.GeneralLinear n ℝ) := by
  apply Units.ext
  rw [matrixExpUnit_val, Matrix.exp_diagonal, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]
  congr 1
  funext i
  simp [Pi.coe_exp, Real.exp_eq_exp_ℝ]

/-- The product of functions in principal series of pointwise inverse characters transforms
by the modulus character. -/
theorem isModulusEquivariant_mul {χ χ' : ℕ → ℝˣ → ℂ} (hχ : ∀ i x, χ i x * χ' i x = 1)
    {f h : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n χ)
    (hh : h ∈ principalSeries ℝ n χ') :
    IsModulusEquivariant fun g => f g * h g := by
  intro x u g
  rw [matrixExpUnit_diagonal]
  set a : Fin n → ℝˣ := fun i => Units.mk0 (Real.exp (x i)) (Real.exp_pos _).ne' with ha
  have hf2 := ((mem_principalSeries_iff ℝ n χ f).mp hf).2 a u g
  have hh2 := ((mem_principalSeries_iff ℝ n χ' h).mp hh).2 a u g
  change f _ * h _ = _
  rw [hf2, hh2]
  have key : principalSeriesCharacter ℝ n χ a * principalSeriesCharacter ℝ n χ' a =
      Complex.exp (∑ i, modulusExponent n i * (x i : ℂ)) := by
    unfold principalSeriesCharacter
    rw [← Finset.prod_mul_distrib, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hn : ‖((a i : ℝˣ) : ℝ)‖ ^ Module.finrank ℝ ℝ = Real.exp (x i) := by
      simp [ha, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hn, ofReal_exp_cpow, mul_mul_mul_comm, hχ, one_mul, ← Complex.exp_add]
    congr 1
    unfold modulusExponent
    ring
  rw [← key]
  ring

end Products

/-! ## The pairing -/

section Pairing

variable {n : ℕ}

theorem continuous_of_mem_kFiniteFunctions {ds : List RealBlock}
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    Continuous f :=
  (contMDiff_of_mem_realStandardModule hf.1).continuous

theorem integrable_mul_of_continuous {f h : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : Continuous f) (hh : Continuous h) :
    Integrable (fun k : unitaryCompact ℝ n =>
      f (k : Langlands.GeneralLinear n ℝ) * h (k : Langlands.GeneralLinear n ℝ)) (haarK n) :=
  integrable_of_continuous ((continuous_comp_val hf).mul (continuous_comp_val hh))

/-- The pairing `⟨f, h⟩ = ∫_{O(n)} f(k) h(k) dk` of `O(n)`-finite functions of two real
standard modules. -/
def pairing (n : ℕ) (ds ds' : List RealBlock) :
    kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun f h => ∫ k, (f : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) *
      (h : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) ∂haarK n)
    (fun f₁ f₂ h => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add
        (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions f₁.2)
          (continuous_of_mem_kFiniteFunctions h.2))
        (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions f₂.2)
          (continuous_of_mem_kFiniteFunctions h.2)))
    (fun c f h => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun f h₁ h₂ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add
        (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions f.2)
          (continuous_of_mem_kFiniteFunctions h₁.2))
        (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions f.2)
          (continuous_of_mem_kFiniteFunctions h₂.2)))
    (fun c f h => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

theorem pairing_apply (ds ds' : List RealBlock)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (h : kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n)) :
    pairing n ds ds' f h =
      ∫ k, (f : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) *
        (h : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) ∂haarK n :=
  rfl

/-- The pairing is invariant under right translation by `O(n)`. -/
theorem pairing_rightTranslation (ds ds' : List RealBlock) (k : unitaryCompact ℝ n)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (h : kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n))
    (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hh : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (h : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n)) :
    pairing n ds ds' ⟨_, hf⟩ ⟨_, hh⟩ = pairing n ds ds' f h := by
  rw [pairing_apply, pairing_apply]
  exact integral_mul_right_eq_self (fun k' : unitaryCompact ℝ n =>
    (f : Langlands.GeneralLinear n ℝ → ℂ) (k' : Langlands.GeneralLinear n ℝ) *
      (h : Langlands.GeneralLinear n ℝ → ℂ) (k' : Langlands.GeneralLinear n ℝ)) k

/-- The pairing is invariant under right derivatives when the position characters are
pointwise inverse. -/
theorem pairing_rightDerivative (ds ds' : List RealBlock)
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (h : kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n))
    (hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hh : rightDerivative (matrixModel ℝ n) X (h : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n)) :
    pairing n ds ds' ⟨_, hf⟩ h + pairing n ds ds' f ⟨_, hh⟩ = 0 := by
  have hfs := contMDiff_of_mem_realStandardModule f.2.1
  have hhs := contMDiff_of_mem_realStandardModule h.2.1
  have hfp := realStandardModule_le_principalSeries n ds f.2.1
  have hhp := realStandardModule_le_principalSeries n ds' h.2.1
  rw [pairing_apply, pairing_apply]
  rw [← integral_add
    (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions hf)
      (continuous_of_mem_kFiniteFunctions h.2))
    (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions f.2)
      (continuous_of_mem_kFiniteFunctions hh))]
  rw [← integral_rightDerivative_eq_zero (contMDiff_mul_fun hfs hhs)
    (isModulusEquivariant_mul hχ hfp hhp) X]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  exact (rightDerivative_mul_fun hfs hhs X _).symm

end Pairing

/-! ## A spherical function -/

section Spherical

variable {n : ℕ}

/-- The diagonal projection onto the coordinates `i ≥ m`. -/
def tailProj (n m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => if m ≤ (i : ℕ) then 1 else 0

/-- The diagonal projection onto the coordinates `i < m`. -/
def headProj (n m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => if m ≤ (i : ℕ) then 0 else 1

theorem tailProj_mul_tailProj (m : ℕ) : tailProj n m * tailProj n m = tailProj n m := by
  rw [tailProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem headProj_mul_headProj (m : ℕ) : headProj n m * headProj n m = headProj n m := by
  rw [headProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem tailProj_mul_headProj (m : ℕ) : tailProj n m * headProj n m = 0 := by
  rw [tailProj, headProj, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext i
  split_ifs <;> simp

theorem headProj_mul_tailProj (m : ℕ) : headProj n m * tailProj n m = 0 := by
  rw [tailProj, headProj, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext i
  split_ifs <;> simp

theorem tailProj_add_headProj (m : ℕ) : tailProj n m + headProj n m = 1 := by
  rw [tailProj, headProj, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem tailProj_transpose (m : ℕ) : (tailProj n m)ᵀ = tailProj n m :=
  Matrix.diagonal_transpose _

theorem headProj_transpose (m : ℕ) : (headProj n m)ᵀ = headProj n m :=
  Matrix.diagonal_transpose _

/-- `P_m(y) = D_m y yᵀ D_m + (1 - D_m)`: the Gram matrix of the rows `i ≥ m` of `y`, padded by
the identity in the coordinates `i < m`. -/
def paddedGram (m : ℕ) (y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  tailProj n m * (y * yᵀ) * tailProj n m + headProj n m

/-- The determinant of `P_m(y)`, the Gram determinant of the rows `i ≥ m` of `y`. -/
def minorDet (m : ℕ) (y : Matrix (Fin n) (Fin n) ℝ) : ℝ := (paddedGram m y).det

theorem paddedGram_mul_orth (m : ℕ) (y : Matrix (Fin n) (Fin n) ℝ)
    {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) : paddedGram m (y * k) = paddedGram m y := by
  have e : y * k * (y * k)ᵀ = y * yᵀ := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k, hk, Matrix.one_mul]
  rw [paddedGram, paddedGram, e]

theorem paddedGram_orth (m : ℕ) {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) :
    paddedGram m k = 1 := by
  rw [paddedGram, hk, Matrix.mul_one, tailProj_mul_tailProj, tailProj_add_headProj]

theorem minorDet_mul_orth (m : ℕ) (y : Matrix (Fin n) (Fin n) ℝ)
    {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) : minorDet m (y * k) = minorDet m y := by
  rw [minorDet, minorDet, paddedGram_mul_orth m y hk]

theorem minorDet_orth (m : ℕ) {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) :
    minorDet m k = 1 := by
  rw [minorDet, paddedGram_orth m hk, Matrix.det_one]

/-- For upper triangular `c`, `D_m c = D_m c D_m`. -/
theorem tailProj_mul_upper (m : ℕ) {c : Matrix (Fin n) (Fin n) ℝ} (hc : c.IsUpperTriangular) :
    tailProj n m * c = tailProj n m * c * tailProj n m := by
  ext i j
  simp only [tailProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : m ≤ (i : ℕ)
  · by_cases hj : m ≤ (j : ℕ)
    · simp [hi, hj]
    · have hji : j < i := Fin.lt_def.mpr (by omega)
      simp [hi, hj, hc hji]
  · simp [hi]

theorem upper_transpose_mul_tailProj (m : ℕ) {c : Matrix (Fin n) (Fin n) ℝ}
    (hc : c.IsUpperTriangular) :
    cᵀ * tailProj n m = tailProj n m * cᵀ * tailProj n m := by
  have h := congrArg Matrix.transpose (tailProj_mul_upper m hc)
  simpa only [Matrix.transpose_mul, tailProj_transpose, Matrix.mul_assoc] using h

/-- The factor `B = D_m c D_m + (1 - D_m)` with `P_m(c y) = B P_m(y) Bᵀ`. -/
def blockFactor (m : ℕ) (c : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  tailProj n m * c * tailProj n m + headProj n m

theorem blockFactor_apply (m : ℕ) (c : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    blockFactor m c i j =
      (if m ≤ (i : ℕ) then 1 else 0) * c i j * (if m ≤ (j : ℕ) then 1 else 0) +
        if i = j then (if m ≤ (i : ℕ) then 0 else 1) else 0 := by
  simp only [blockFactor, tailProj, headProj, Matrix.add_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.diagonal_apply]

theorem paddedGram_upper_mul (m : ℕ) {c : Matrix (Fin n) (Fin n) ℝ} (hc : c.IsUpperTriangular)
    (y : Matrix (Fin n) (Fin n) ℝ) :
    paddedGram m (c * y) = blockFactor m c * paddedGram m y * (blockFactor m c)ᵀ := by
  have hDD' : ∀ X : Matrix (Fin n) (Fin n) ℝ, tailProj n m * (tailProj n m * X) =
      tailProj n m * X := fun X => by
    rw [← Matrix.mul_assoc, tailProj_mul_tailProj]
  have hEE' : ∀ X : Matrix (Fin n) (Fin n) ℝ, headProj n m * (headProj n m * X) =
      headProj n m * X := fun X => by
    rw [← Matrix.mul_assoc, headProj_mul_headProj]
  have hDE' : ∀ X : Matrix (Fin n) (Fin n) ℝ, tailProj n m * (headProj n m * X) = 0 :=
    fun X => by rw [← Matrix.mul_assoc, tailProj_mul_headProj, Matrix.zero_mul]
  have hED' : ∀ X : Matrix (Fin n) (Fin n) ℝ, headProj n m * (tailProj n m * X) = 0 :=
    fun X => by rw [← Matrix.mul_assoc, headProj_mul_tailProj, Matrix.zero_mul]
  have h1 := tailProj_mul_upper m hc
  have h2 := upper_transpose_mul_tailProj m hc
  have hBt : (blockFactor m c)ᵀ = tailProj n m * cᵀ * tailProj n m + headProj n m := by
    rw [blockFactor, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      tailProj_transpose, headProj_transpose, Matrix.mul_assoc]
  calc paddedGram m (c * y) =
        (tailProj n m * c) * (y * yᵀ) * (cᵀ * tailProj n m) + headProj n m := by
        simp only [paddedGram, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (tailProj n m * c * tailProj n m) * (y * yᵀ) * (tailProj n m * cᵀ * tailProj n m) +
          headProj n m := by rw [← h1, ← h2]
    _ = blockFactor m c * paddedGram m y * (blockFactor m c)ᵀ := by
        rw [hBt, blockFactor, paddedGram]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, headProj_mul_headProj,
          tailProj_mul_headProj, hDD', hED', Matrix.mul_zero, add_zero, zero_add]

theorem det_blockFactor (m : ℕ) {c : Matrix (Fin n) (Fin n) ℝ} (hc : c.IsUpperTriangular) :
    (blockFactor m c).det = ∏ i : Fin n, if m ≤ (i : ℕ) then c i i else 1 := by
  have hB : (blockFactor m c).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    rw [blockFactor_apply, hc hij]
    simp [(ne_of_lt hij).symm]
  rw [Matrix.det_of_isUpperTriangular hB]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [blockFactor_apply]
  by_cases h : m ≤ (i : ℕ) <;> simp [h]

/-- `det P_m(c y) = (∏_{i ≥ m} cᵢᵢ)² det P_m(y)` for upper triangular `c`. -/
theorem minorDet_upper_mul (m : ℕ) {c : Matrix (Fin n) (Fin n) ℝ} (hc : c.IsUpperTriangular)
    (y : Matrix (Fin n) (Fin n) ℝ) :
    minorDet m (c * y) = (∏ i : Fin n, if m ≤ (i : ℕ) then c i i else 1) ^ 2 * minorDet m y := by
  rw [minorDet, minorDet, paddedGram_upper_mul m hc, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_blockFactor m hc]
  ring

/-- `∏_{i ≥ j} cᵢᵢ = c_jj ∏_{i ≥ j + 1} cᵢᵢ`. -/
theorem prod_tail_succ (c : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (∏ i : Fin n, if (j : ℕ) ≤ (i : ℕ) then c i i else 1) =
      c j j * ∏ i : Fin n, if (j : ℕ) + 1 ≤ (i : ℕ) then c i i else 1 := by
  have e : ∀ i : Fin n, (if (j : ℕ) ≤ (i : ℕ) then c i i else 1) =
      (if i = j then c i i else 1) * (if (j : ℕ) + 1 ≤ (i : ℕ) then c i i else 1) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp
    · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      by_cases h : (j : ℕ) ≤ (i : ℕ)
      · have h' : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
        simp only [h, hij, h', ↓reduceIte, one_mul]
      · have h' : ¬(j : ℕ) + 1 ≤ (i : ℕ) := by omega
        simp only [h, hij, h', ↓reduceIte, one_mul]
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

/-- The Gram determinants of invertible matrices are positive (Iwasawa: `y = b u`). -/
theorem minorDet_pos (m : ℕ) {y : Matrix (Fin n) (Fin n) ℝ} (hy : IsUnit y) :
    0 < minorDet m y := by
  obtain ⟨b, u, hb, hbu, hu, rfl⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary y hy
  have huu : u * uᵀ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hu
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hdet : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det b).mp hbu).ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  have hd : ∀ i, b i i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
  have hp : (∏ i : Fin n, if m ≤ (i : ℕ) then b i i else 1) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    split_ifs
    · exact hd i
    · exact one_ne_zero
  rw [minorDet_upper_mul m hb, minorDet_orth m huu, mul_one]
  positivity

/-- The Gram determinants are polynomial in the entries. -/
theorem contDiff_det (k : WithTop ℕ∞) :
    ContDiff ℝ k fun M : Matrix (Fin n) (Fin n) ℝ => M.det := by
  have he : ∀ i j : Fin n, ContDiff ℝ k fun M : Matrix (Fin n) (Fin n) ℝ => M i j := fun i j =>
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
        Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)).contDiff
  have e : (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) = fun M =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i :=
    funext fun M => Matrix.det_apply' M
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => he (σ i) i)

theorem contDiff_paddedGram (k : WithTop ℕ∞) (m : ℕ) :
    ContDiff ℝ k (paddedGram (n := n) m) := by
  let T : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ := LinearMap.toContinuousLinearMap
    { toFun := Matrix.transpose, map_add' := Matrix.transpose_add,
      map_smul' := fun c A => Matrix.transpose_smul c A }
  have hT : ContDiff ℝ k fun y : Matrix (Fin n) (Fin n) ℝ => yᵀ := T.contDiff
  unfold paddedGram
  exact ((contDiff_const.mul (contDiff_id.mul hT)).mul contDiff_const).add contDiff_const

theorem contDiff_minorDet (k : WithTop ℕ∞) (m : ℕ) :
    ContDiff ℝ k (minorDet (n := n) m) :=
  (contDiff_det k).comp (contDiff_paddedGram k m)

/-- `y ↦ ∏_j (det P_j(y) / det P_{j+1}(y))^{r_j/2}`, equal to `∏_j |b_jj|^{r_j}` for `y = b u`
with `b` upper triangular and `u` orthogonal. -/
def sphericalReal (r : Fin n → ℝ) (y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ j : Fin n, (minorDet (j : ℕ) y / minorDet ((j : ℕ) + 1) y) ^ (r j / 2)

theorem contDiffOn_sphericalReal (k : WithTop ℕ∞) (r : Fin n → ℝ) :
    ContDiffOn ℝ k (sphericalReal r) {y : Matrix (Fin n) (Fin n) ℝ | IsUnit y} := by
  unfold sphericalReal
  refine contDiffOn_prod fun j _ => ?_
  refine ContDiffOn.rpow_const_of_ne ?_ ?_
  · exact (contDiff_minorDet k _).contDiffOn.div (contDiff_minorDet k _).contDiffOn
      fun y hy => (minorDet_pos _ hy).ne'
  · intro y hy
    exact (div_pos (minorDet_pos _ hy) (minorDet_pos _ hy)).ne'

theorem sphericalReal_mul_orth (r : Fin n → ℝ) (y : Matrix (Fin n) (Fin n) ℝ)
    {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) :
    sphericalReal r (y * k) = sphericalReal r y := by
  simp only [sphericalReal, minorDet_mul_orth _ y hk]

theorem sphericalReal_orth (r : Fin n → ℝ) {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) :
    sphericalReal r k = 1 := by
  simp [sphericalReal, minorDet_orth _ hk]

theorem sphericalReal_upper_mul (r : Fin n → ℝ) {c : Matrix (Fin n) (Fin n) ℝ}
    (hc : c.IsUpperTriangular) (hd : ∀ i, c i i ≠ 0) {y : Matrix (Fin n) (Fin n) ℝ}
    (hy : IsUnit y) :
    sphericalReal r (c * y) = (∏ j : Fin n, |c j j| ^ r j) * sphericalReal r y := by
  unfold sphericalReal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hp : (∏ i : Fin n, if (j : ℕ) + 1 ≤ (i : ℕ) then c i i else 1) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    split_ifs
    · exact hd i
    · exact one_ne_zero
  have h0 := minorDet_pos (j : ℕ) hy
  have h1 := minorDet_pos ((j : ℕ) + 1) hy
  have hq : minorDet (j : ℕ) (c * y) / minorDet ((j : ℕ) + 1) (c * y) =
      |c j j| ^ (2 : ℝ) * (minorDet (j : ℕ) y / minorDet ((j : ℕ) + 1) y) := by
    rw [minorDet_upper_mul _ hc, minorDet_upper_mul _ hc, prod_tail_succ c j, Real.rpow_two,
      sq_abs]
    field_simp
  rw [hq, Real.mul_rpow (by positivity) (div_pos h0 h1).le, ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  ring

end Spherical

/-! ## The spherical function on `GL_n(ℝ)` -/

section SphericalGL

variable {n : ℕ}

/-- The complex-valued function `g ↦ sphericalReal r g` on `GL_n(ℝ)`. -/
def spherical (r : Fin n → ℝ) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ((sphericalReal r (g : Matrix (Fin n) (Fin n) ℝ) : ℝ) : ℂ)

theorem contMDiff_spherical (r : Fin n → ℝ) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (spherical r) :=
  contMDiff_of_contDiffOn (ψ := Complex.ofRealCLM ∘ sphericalReal r)
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_sphericalReal ∞ r))
    fun _ => rfl

/-- `k kᵀ = 1` for `k ∈ O(n)`. -/
theorem mul_transpose_self_of_mem (k : unitaryCompact ℝ n) :
    ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) *
      (((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))ᵀ = 1 :=
  mul_eq_one_comm.mp (transpose_mul_self_of_mem k)

theorem spherical_mul_mem (r : Fin n → ℝ) (g : Langlands.GeneralLinear n ℝ)
    (k : unitaryCompact ℝ n) :
    spherical r (g * (k : Langlands.GeneralLinear n ℝ)) = spherical r g := by
  unfold spherical
  rw [Units.val_mul, sphericalReal_mul_orth r _ (mul_transpose_self_of_mem k)]

theorem spherical_mem (r : Fin n → ℝ) (k : unitaryCompact ℝ n) :
    spherical r (k : Langlands.GeneralLinear n ℝ) = 1 := by
  unfold spherical
  rw [sphericalReal_orth r (mul_transpose_self_of_mem k), Complex.ofReal_one]

/-- `φ_r(diag(a) u g) = (∏ⱼ |aⱼ|^{rⱼ}) φ_r(g)` for `u` upper unipotent. -/
theorem spherical_diagonal_mul (r : Fin n → ℝ) (a : Fin n → ℝˣ)
    (u : Langlands.GeneralLinear.upperUnipotent n ℝ) (g : Langlands.GeneralLinear n ℝ) :
    spherical r ((Langlands.GeneralLinear.Iwasawa.diagonalUnits a :
        Langlands.GeneralLinear n ℝ) * (u : Langlands.GeneralLinear n ℝ) * g) =
      ((∏ j : Fin n, |((a j : ℝˣ) : ℝ)| ^ r j : ℝ) : ℂ) * spherical r g := by
  unfold spherical
  have hc : ((Matrix.diagonal fun i => ((a i : ℝˣ) : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)).IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).mul u.2.1
  have hd : ∀ j, ((Matrix.diagonal fun i => ((a i : ℝˣ) : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) j j = ((a j : ℝˣ) : ℝ) := by
    intro j
    have h1 : ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) j j = 1 := u.2.2 j
    rw [Matrix.diagonal_mul, h1, mul_one]
  rw [Units.val_mul, Units.val_mul, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val,
    sphericalReal_upper_mul r hc (fun j => by rw [hd]; exact (a j).ne_zero) (Units.isUnit g),
    Complex.ofReal_mul]
  simp only [hd]

end SphericalGL

/-! ## Nondegeneracy -/

section Nondegeneracy

variable {n : ℕ}

/-- `|χ(x)| = |x|^{Re s}` for a real character with exponent `s`. -/
theorem norm_character (c : RealCharacterData) (x : ℝˣ) :
    ‖(c.character x : ℂ)‖ = |(x : ℝ)| ^ c.exponent.re := by
  have hx : 0 < |(x : ℝ)| := abs_pos.mpr x.ne_zero
  have h1 : ‖((((x : ℝ) / |(x : ℝ)| : ℝ)) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs, div_self hx.ne']
  rw [c.character_eq, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, h1, one_pow,
    one_mul]

/-- The position characters of real character blocks have absolute value a power of `|x|`. -/
theorem exists_norm_realPositionCharacter (cs : List RealCharacterData) (i : ℕ) :
    ∃ σ : ℝ, ∀ x : ℝˣ,
      ‖realPositionCharacter (cs.map RealBlock.character) i x‖ = |(x : ℝ)| ^ σ := by
  induction cs generalizing i with
  | nil => exact ⟨0, fun x => by simp [realPositionCharacter]⟩
  | cons c cs ih =>
    cases i with
    | zero => exact ⟨c.exponent.re, fun x => by
        simp only [List.map_cons, realPositionCharacter]
        exact norm_character c x⟩
    | succ i =>
      obtain ⟨σ, hσ⟩ := ih i
      exact ⟨σ, fun x => by
        simp only [List.map_cons, realPositionCharacter]
        exact hσ x⟩

/-- Real character blocks contain no induction blocks. -/
theorem realInducedBlockAt_map_character (cs : List RealCharacterData) (p : ℕ) :
    realInducedBlockAt (cs.map RealBlock.character) p = none := by
  induction cs generalizing p with
  | nil => simp [realInducedBlockAt]
  | cons c cs ih =>
    cases p with
    | zero => simp [realInducedBlockAt]
    | succ p => simp [realInducedBlockAt, ih]

/-- If `w z = 1` and `|z| = |x|^s`, then `conj(z) |x|^{-2s} = w`. -/
theorem conj_mul_rpow {z w : ℂ} {x : ℝˣ} {s : ℝ} (hzw : w * z = 1)
    (hz : ‖z‖ = |(x : ℝ)| ^ s) :
    starRingEnd ℂ z * ((|(x : ℝ)| ^ (-(2 * s)) : ℝ) : ℂ) = w := by
  have hz0 : z ≠ 0 := right_ne_zero_of_mul_eq_one hzw
  have hx : 0 < |(x : ℝ)| := abs_pos.mpr x.ne_zero
  have key : (|(x : ℝ)| ^ s) ^ 2 * |(x : ℝ)| ^ (-(2 * s)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx,
      show s * ((2 : ℕ) : ℝ) + -(2 * s) = 0 by push_cast; ring, Real.rpow_zero]
  apply mul_right_cancel₀ hz0
  rw [hzw]
  calc starRingEnd ℂ z * ((|(x : ℝ)| ^ (-(2 * s)) : ℝ) : ℂ) * z
      = (starRingEnd ℂ z * z) * ((|(x : ℝ)| ^ (-(2 * s)) : ℝ) : ℂ) := by ring
    _ = (((|(x : ℝ)| ^ s) ^ 2 * |(x : ℝ)| ^ (-(2 * s)) : ℝ) : ℂ) := by
        rw [Complex.conj_mul', hz, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    _ = 1 := by rw [key, Complex.ofReal_one]

/-- `conj(δ_{χ'}(a)) ∏ⱼ |aⱼ|^{-2σⱼ} = δ_χ(a)` when `χᵢ χ'ᵢ = 1` and `|χ'ᵢ(x)| = |x|^{σᵢ}`. -/
theorem principalSeriesCharacter_conj_mul {χ χ' : ℕ → ℝˣ → ℂ} {σ : ℕ → ℝ}
    (hχ : ∀ i x, χ i x * χ' i x = 1) (hσ : ∀ i x, ‖χ' i x‖ = |(x : ℝ)| ^ σ i)
    (a : Fin n → ℝˣ) :
    starRingEnd ℂ (principalSeriesCharacter ℝ n χ' a) *
        ((∏ j : Fin n, |((a j : ℝˣ) : ℝ)| ^ (-(2 * σ j)) : ℝ) : ℂ) =
      principalSeriesCharacter ℝ n χ a := by
  unfold principalSeriesCharacter
  rw [map_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ht : 0 ≤ ‖((a i : ℝˣ) : ℝ)‖ ^ Module.finrank ℝ ℝ := by positivity
  have hw : ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) =
      (((((n : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hw, ← Complex.ofReal_cpow ht, map_mul, Complex.conj_ofReal, mul_right_comm,
    conj_mul_rpow (hχ i (a i)) (hσ i (a i))]

/-- `v ↦ conj(v) φ_r`, a conjugate-linear map of functions on `GL_n(ℝ)`. -/
def conjMulSpherical (r : Fin n → ℝ) :
    (Langlands.GeneralLinear n ℝ → ℂ) →ₛₗ[starRingEnd ℂ] (Langlands.GeneralLinear n ℝ → ℂ) where
  toFun v g := starRingEnd ℂ (v g) * spherical r g
  map_add' v w := by
    funext g
    simp only [Pi.add_apply, map_add, add_mul]
  map_smul' c v := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem conjMulSpherical_apply (r : Fin n → ℝ) (v : Langlands.GeneralLinear n ℝ → ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    conjMulSpherical r v g = starRingEnd ℂ (v g) * spherical r g :=
  rfl

theorem contMDiff_conjMulSpherical (r : Fin n → ℝ) {v : Langlands.GeneralLinear n ℝ → ℂ}
    (hv : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ v) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (conjMulSpherical r v) :=
  contMDiff_mul_fun (Complex.conjCLE.contDiff.contMDiff.comp hv) (contMDiff_spherical r)

theorem conjMulSpherical_rightTranslation (r : Fin n → ℝ) (k : unitaryCompact ℝ n)
    (v : Langlands.GeneralLinear n ℝ → ℂ) :
    conjMulSpherical r (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) v) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (conjMulSpherical r v) := by
  funext g
  change starRingEnd ℂ (v (g * (k : Langlands.GeneralLinear n ℝ))) * spherical r g =
    starRingEnd ℂ (v (g * (k : Langlands.GeneralLinear n ℝ))) *
      spherical r (g * (k : Langlands.GeneralLinear n ℝ))
  rw [spherical_mul_mem]

theorem conjMulSpherical_mem_kFiniteVectors (r : Fin n → ℝ)
    {v : Langlands.GeneralLinear n ℝ → ℂ}
    (hv : v ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    conjMulSpherical r v ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
        (unitaryCompact ℝ n) := by
  rw [mem_kFiniteVectors_iff] at hv ⊢
  have e : (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (conjMulSpherical r v)) =
      conjMulSpherical r '' Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) v := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun k => (conjMulSpherical_rightTranslation r k v).symm)
  rw [e, ← Submodule.map_span]
  have hfg := (Submodule.fg_iff_finiteDimensional _).mpr hv
  exact (Submodule.fg_iff_finiteDimensional _).mp (hfg.map (conjMulSpherical r))

/-- `conj(h) φ_r` lies in the principal series of `χ` when `h` lies in that of `χ'`. -/
theorem conjMulSpherical_mem_principalSeries {χ χ' : ℕ → ℝˣ → ℂ} {σ : ℕ → ℝ}
    (hχ : ∀ i x, χ i x * χ' i x = 1) (hσ : ∀ i x, ‖χ' i x‖ = |(x : ℝ)| ^ σ i)
    {h : Langlands.GeneralLinear n ℝ → ℂ} (hh : h ∈ principalSeries ℝ n χ') :
    conjMulSpherical (fun j : Fin n => -(2 * σ j)) h ∈ principalSeries ℝ n χ := by
  rw [mem_principalSeries_iff] at hh ⊢
  refine ⟨contMDiff_conjMulSpherical _ hh.1, fun a u g => ?_⟩
  rw [conjMulSpherical_apply, conjMulSpherical_apply, hh.2 a u g, spherical_diagonal_mul,
    map_mul, ← principalSeriesCharacter_conj_mul hχ hσ a]
  ring

/-- A nonzero function of a principal series is nonzero somewhere on `O(n)` (Iwasawa
decomposition). -/
theorem exists_mem_unitaryCompact_ne_zero {χ : ℕ → ℝˣ → ℂ}
    {h : Langlands.GeneralLinear n ℝ → ℂ} (hh : h ∈ principalSeries ℝ n χ)
    {g : Langlands.GeneralLinear n ℝ} (hg : h g ≠ 0) :
    ∃ k : unitaryCompact ℝ n, h (k : Langlands.GeneralLinear n ℝ) ≠ 0 := by
  obtain ⟨b, u, hb, hbu, hu, hgbu⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary
      (g : Matrix (Fin n) (Fin n) ℝ) (Units.isUnit g)
  have hdet : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det b).mp hbu).ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  have hd : ∀ i, b i i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
  let a : Fin n → ℝˣ := fun i => Units.mk0 (b i i) (hd i)
  let D : Langlands.GeneralLinear n ℝ := Langlands.GeneralLinear.Iwasawa.diagonalUnits a
  let U : unitaryCompact ℝ n := ⟨Unitary.toUnits ⟨u, hu⟩, hu⟩
  have hv : D⁻¹ * hbu.unit ∈ Langlands.GeneralLinear.upperUnipotent n ℝ := by
    have hval : ((D⁻¹ * hbu.unit : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
        (Matrix.diagonal fun i => (((a i)⁻¹ : ℝˣ) : ℝ)) * b := by
      rw [Units.val_mul, IsUnit.unit_spec]
      rfl
    refine ⟨?_, fun i => ?_⟩
    · change ((D⁻¹ * hbu.unit : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular
      rw [hval]
      exact (Matrix.blockTriangular_diagonal _).mul hb
    · change ((D⁻¹ * hbu.unit : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i i = 1
      rw [hval, Matrix.diagonal_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact inv_mul_cancel₀ (hd i)
  have hgU : g = D * (⟨_, hv⟩ : Langlands.GeneralLinear.upperUnipotent n ℝ) *
      (U : Langlands.GeneralLinear n ℝ) := by
    change g = D * (D⁻¹ * hbu.unit) * (U : Langlands.GeneralLinear n ℝ)
    rw [mul_inv_cancel_left]
    apply Units.ext
    rw [Units.val_mul, IsUnit.unit_spec]
    exact hgbu
  refine ⟨U, fun h0 => hg ?_⟩
  rw [hgU, ((mem_principalSeries_iff ℝ n χ h).mp hh).2 a, h0, mul_zero]

/-- The pairing is nondegenerate in the second argument: `⟨conj(h) φ_r, h⟩ = ∫_{O(n)} |h|²`. -/
theorem exists_pairing_ne_zero (cs cs' : List RealCharacterData)
    (hχ : ∀ (i : ℕ) (x : ℝˣ),
      realPositionCharacter (cs.map RealBlock.character) i x *
        realPositionCharacter (cs'.map RealBlock.character) i x = 1)
    (h : kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character))
      (unitaryCompact ℝ n))
    (hh0 : h ≠ 0) :
    ∃ f, pairing n (cs.map RealBlock.character) (cs'.map RealBlock.character) f h ≠ 0 := by
  choose σ hσ using exists_norm_realPositionCharacter cs'
  have hhp := realStandardModule_le_principalSeries n _ h.2.1
  have hF : conjMulSpherical (fun j : Fin n => -(2 * σ j)) (h : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
        (unitaryCompact ℝ n) := by
    refine ⟨⟨conjMulSpherical_mem_principalSeries hχ hσ hhp, fun p d hd => ?_⟩,
      conjMulSpherical_mem_kFiniteVectors _ h.2.2⟩
    rw [realInducedBlockAt_map_character] at hd
    exact absurd hd (by simp)
  refine ⟨⟨_, hF⟩, ?_⟩
  obtain ⟨g, hg⟩ : ∃ g, (h : Langlands.GeneralLinear n ℝ → ℂ) g ≠ 0 :=
    Function.ne_iff.mp fun e => hh0 (Subtype.ext e)
  obtain ⟨k₀, hk₀⟩ := exists_mem_unitaryCompact_ne_zero hhp hg
  rw [pairing_apply]
  have hint : (fun k : unitaryCompact ℝ n =>
      conjMulSpherical (fun j : Fin n => -(2 * σ j)) (h : Langlands.GeneralLinear n ℝ → ℂ)
          (k : Langlands.GeneralLinear n ℝ) *
        (h : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ)) =
      fun k : unitaryCompact ℝ n =>
        ((‖(h : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ)‖ ^ 2 :
          ℝ) : ℂ) := by
    funext k
    rw [conjMulSpherical_apply, spherical_mem, mul_one, Complex.conj_mul', Complex.ofReal_pow]
  change ∫ k, (fun k : unitaryCompact ℝ n =>
      conjMulSpherical (fun j : Fin n => -(2 * σ j)) (h : Langlands.GeneralLinear n ℝ → ℂ)
          (k : Langlands.GeneralLinear n ℝ) *
        (h : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ)) k ∂haarK n ≠ 0
  rw [hint, integral_complex_ofReal, Complex.ofReal_ne_zero]
  have hc : Continuous fun k : unitaryCompact ℝ n =>
      ‖(h : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ)‖ ^ 2 :=
    ((continuous_comp_val (continuous_of_mem_kFiniteFunctions h.2)).norm).pow 2
  refine (hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := k₀)
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_).ne'
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hk₀)

end Nondegeneracy

/-! ## The duality theorem -/

/-- **Duality for real principal series.** For lists of real characters whose position
characters are pointwise inverse, `⟨f, h⟩ = ∫_{O(n)} f(k) h(k) dk` is an `O(n)`-invariant and
`𝔤`-invariant pairing of the `O(n)`-finite functions, nondegenerate in the second argument. -/
theorem realPrincipalSeriesDuality : RealPrincipalSeriesDualityStatement := by
  intro n cs cs' hχ
  refine ⟨pairing n (cs.map RealBlock.character) (cs'.map RealBlock.character), ?_, ?_, ?_⟩
  · intro k f h hf hh
    exact pairing_rightTranslation _ _ k f h hf hh
  · intro X f h hf hh
    exact pairing_rightDerivative _ _ hχ X f h hf hh
  · intro h hh0
    exact exists_pairing_ne_zero cs cs' hχ h hh0

end RealPrincipalSeriesDuality

end Langlands.Archimedean
