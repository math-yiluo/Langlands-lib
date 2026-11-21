import Langlands.Representation.Archimedean.RealMixedMatrixCoordinates
import Langlands.Representation.Archimedean.SmoothOrthonormalSquareSum
import Langlands.Representation.Archimedean.MixedOrbitCoefficient
import Langlands.Global.ArchimedeanCompactComponentCoverageProof

/-! # The rational Cartan square sum on actual real general linear groups -/

noncomputable section

open Set
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.Global Langlands.Global.ArchimedeanGL

/-- Unitary conjugation preserves the positive Cartan form of the mixed matrix algebra. -/
theorem cartanPositiveForm_star_conj (K : Type*) [Field K] [NumberField K] (n : ℕ)
    {u : ArchimedeanMatrix K n} (hu : u * star u = 1) (X Y : ArchimedeanMatrix K n) :
    cartanPositiveForm K n ((realLieAlgebraToMatrix K n).symm (star u * X * u))
        ((realLieAlgebraToMatrix K n).symm (star u * Y * u)) =
      cartanPositiveForm K n ((realLieAlgebraToMatrix K n).symm X)
        ((realLieAlgebraToMatrix K n).symm Y) := by
  change totalMixedTrace K (Matrix.trace ((star u * X * u) * star (star u * Y * u))) =
    totalMixedTrace K (Matrix.trace (X * star Y))
  congr 1
  have h1 : star (star u * Y * u) = star u * star Y * u := by
    rw [star_mul, star_mul, star_star, mul_assoc]
  rw [h1]
  have h2 : star u * X * u * (star u * star Y * u) = star u * (X * star Y * u) := by
    rw [show star u * X * u * (star u * star Y * u) = star u * X * (u * star u) * star Y * u by
      simp only [mul_assoc], hu, mul_one]
    simp only [mul_assoc]
  rw [h2, Matrix.trace_mul_comm, mul_assoc, hu, mul_one]

namespace RealCartan

variable (n : ℕ)

local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "GLR" => Langlands.GeneralLinear n ℝ
local notation "ψ" => rationalMixedMatrixEquiv n

/-- The rational real Lie algebra identified with actual real matrices. -/
def realCartanEquiv : RealLieAlgebra ℚ n ≃ₗ[ℝ] M :=
  (realLieAlgebraToMatrix ℚ n).trans (rationalMixedMatrixEquiv n).toLinearEquiv

/-- The positive Cartan form transported to actual real matrices. -/
def realCartanForm : LinearMap.BilinForm ℝ M :=
  (cartanPositiveForm ℚ n).compl₁₂ (realCartanEquiv n).symm.toLinearMap
    (realCartanEquiv n).symm.toLinearMap

/-- The normalized Cartan basis transported to actual real matrices. -/
def realCartanBasis : Module.Basis (CartanBasisIndex ℚ n) ℝ M :=
  (cartanAdaptedBasis ℚ n).map (realCartanEquiv n)

theorem realCartanForm_symm (X Y : M) : realCartanForm n X Y = realCartanForm n Y X := by
  simp only [realCartanForm, LinearMap.compl₁₂_apply]
  exact cartanPositiveForm_symm ℚ n _ _

theorem realCartanBasis_pair (i j : CartanBasisIndex ℚ n) :
    realCartanForm n (realCartanBasis n i) (realCartanBasis n j) = if i = j then 1 else 0 := by
  simp only [realCartanForm, LinearMap.compl₁₂_apply, realCartanBasis, Module.Basis.map_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact cartanAdaptedBasis_pair ℚ n i j

/-- Inverse conjugation by an orthogonal matrix preserves the transported Cartan form. -/
theorem realCartanForm_conj {k : GLR} (hk : k ∈ unitaryCompact ℝ n) (X Y : M) :
    realCartanForm n (DerivativeSmoothVectors.inverseConjugationCLM k X)
        (DerivativeSmoothVectors.inverseConjugationCLM k Y) = realCartanForm n X Y := by
  have hk' : (k : M) ∈ Matrix.unitaryGroup (Fin n) ℝ := hk
  have hinv : ((k⁻¹ : GLR) : M) = star (k : M) :=
    Units.inv_eq_of_mul_eq_one_left (Unitary.star_mul_self_of_mem hk')
  let u : ArchimedeanMatrix ℚ n := (ψ).symm (k : M)
  have hstar (Z : M) : (ψ).symm (star Z) = star ((ψ).symm Z) := by
    apply (ψ).injective
    rw [AlgEquiv.apply_symm_apply, rationalMixedMatrixEquiv_star, AlgEquiv.apply_symm_apply]
  have hu : u * star u = 1 := by
    simp only [u, ← hstar, ← map_mul, Unitary.mul_star_self_of_mem hk', map_one]
  have hc (Z : M) : (ψ).symm (DerivativeSmoothVectors.inverseConjugationCLM k Z) =
      star u * (ψ).symm Z * u := by
    rw [DerivativeSmoothVectors.inverseConjugationCLM_apply, map_mul, map_mul, hinv, hstar]
  change cartanPositiveForm ℚ n ((realLieAlgebraToMatrix ℚ n).symm
      ((ψ).symm (DerivativeSmoothVectors.inverseConjugationCLM k X)))
      ((realLieAlgebraToMatrix ℚ n).symm
        ((ψ).symm (DerivativeSmoothVectors.inverseConjugationCLM k Y))) =
    cartanPositiveForm ℚ n ((realLieAlgebraToMatrix ℚ n).symm ((ψ).symm X))
      ((realLieAlgebraToMatrix ℚ n).symm ((ψ).symm Y))
  rw [hc, hc, cartanPositiveForm_star_conj ℚ n hu]

theorem transportedCartanSquareSum_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E)) :
    MixedOrbit.transportedCartanSquareSum ℚ n (rationalMixedMatrixEquiv n) R =
      DerivativeSmoothVectors.basisSquareSum R (realCartanBasis n) := by
  simp only [MixedOrbit.transportedCartanSquareSum, DerivativeSmoothVectors.basisSquareSum,
    realCartanBasis, Module.Basis.map_apply]
  rfl

/-- The transported Cartan square sum commutes with the actual orthogonal action. -/
theorem transportedCartanSquareSum_representation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n)
    (w : DerivativeSmoothVectors (matrixModel ℝ n) R) :
    MixedOrbit.transportedCartanSquareSum ℚ n (rationalMixedMatrixEquiv n) R
        (DerivativeSmoothVectors.representation (matrixModel ℝ n) R k w) =
      DerivativeSmoothVectors.representation (matrixModel ℝ n) R k
        (MixedOrbit.transportedCartanSquareSum ℚ n (rationalMixedMatrixEquiv n) R w) := by
  rw [transportedCartanSquareSum_eq]
  exact DerivativeSmoothVectors.basisSquareSum_representation R (realCartanForm n)
    (realCartanForm_symm n) (realCartanBasis n) (realCartanBasis_pair n) k
    (realCartanForm_conj n hk) w

/-- Every connected component of the rational completion-based group meets the preimage of the
actual orthogonal group. -/
theorem exists_unitaryCompact_mem_connectedComponent
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing ℚ)) :
    ∃ x₀, x ∈ connectedComponent x₀ ∧
      MixedOrbit.unitsMap ℚ n ψ (archimedeanGLCoordinates ℚ n x₀) ∈ unitaryCompact ℝ n := by
  let F := fun y : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing ℚ) =>
    MixedOrbit.unitsMap ℚ n ψ (archimedeanGLCoordinates ℚ n y)
  let G := fun g : GLR => (archimedeanGLCoordinates ℚ n).symm ((rationalMixedUnitsEquiv n).symm g)
  have hG : Continuous G :=
    (archimedeanGLCoordinates ℚ n).symm.continuous.comp
      (contMDiff_rationalMixedUnitsEquiv_symm n).continuous
  have hFG (g : GLR) : F (G g) = g := by
    apply Units.ext
    simp only [F, G, ContinuousMulEquiv.apply_symm_apply, MixedOrbit.unitsMap_val,
      rationalMixedUnitsEquiv_symm_val, AlgEquiv.apply_symm_apply]
  have hGF (y : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing ℚ)) :
      G (F y) = y := by
    have h : (rationalMixedUnitsEquiv n).symm (F y) = archimedeanGLCoordinates ℚ n y := by
      apply Units.ext
      simp only [F, rationalMixedUnitsEquiv_symm_val, MixedOrbit.unitsMap_val,
        AlgEquiv.symm_apply_apply]
    simp only [G, h, ContinuousMulEquiv.symm_apply_apply]
  obtain ⟨U, hU, hmem⟩ := exists_unitary_mem_connectedComponent (F x)
  refine ⟨G U, ?_, by change F (G U) ∈ unitaryCompact ℝ n; rw [hFG]; exact hU⟩
  have h := (isPreconnected_connectedComponent.image G hG.continuousOn).subset_connectedComponent
    ⟨U, mem_connectedComponent, rfl⟩
  exact h ⟨F x, hmem, hGF x⟩

end RealCartan

end Langlands.Archimedean
