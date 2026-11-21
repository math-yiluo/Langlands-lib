import Langlands.Representation.Archimedean.SmoothCompactOrbitIntegral
import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Langlands.Representation.CompactRepresentativeWeights
import Mathlib.Analysis.LocallyConvex.Separation

/-! # Compact-finite density in real genuine smooth vectors -/

noncomputable section

open MeasureTheory Set Langlands.CompactRepresentativeWeights
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

open OrthogonalFinitePolynomial

universe u

variable {n : ℕ}

local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "I" => matrixModel ℝ n

private theorem entry_finite (ij : Fin n × Fin n) :
    FiniteVectors.IsFiniteVector leftRegular (entry n ij) := by
  let P := Submodule.span ℂ (range (entry n))
  have : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (Set.finite_range (entry n))
  apply Submodule.finiteDimensional_of_le (S₂ := P)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  have h : leftRegular k (entry n ij) =
      ∑ i : Fin n, ((k⁻¹ : K).val ij.1 i : ℂ) • entry n (i, ij.2) := by
    apply ContinuousMap.ext
    intro x
    simp only [leftRegular_apply, entry_apply, Matrix.UnitaryGroup.mul_val,
      Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change leftRegular k (entry n ij) ∈ P
  rw [h]
  exact Submodule.sum_mem P fun i _ =>
    P.smul_mem _ (Submodule.subset_span (mem_range_self (i, ij.2)))

private theorem polynomial_le_finiteWeights :
    polynomialStar n ≤ (finiteWeights : StarSubalgebra ℂ C(K, ℂ)) := by
  apply StarAlgebra.adjoin_le_iff.mpr
  rintro _ ⟨ij, rfl⟩
  exact entry_finite ij

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
  (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)) [μ.IsHaarMeasure]

local notation "D[" P "]" => DerivativeSmoothVectors I P

private def orthogonalInclusion : C(K, G) :=
  ⟨Unitary.toUnits, continuous_unitary_toUnits⟩

omit [CompleteSpace E] in
private theorem injective_emptyWord (P : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E)) :
    Function.Injective (derivativeCLM (matrixModel ℝ n) P []) := by
  intro x y h
  apply (toSmooth (matrixModel ℝ n) P).injective
  apply Subtype.ext
  simpa only [derivativeCLM_apply, iteratedLieDerivative_nil] using h

omit [CompleteSpace E] in
private theorem derivativeCLM_nil_representation (g : G) (v : D[R]) :
    derivativeCLM I R [] (representation I R g v) = R g (derivativeCLM I R [] v) := by
  simp only [derivativeCLM_apply, iteratedLieDerivative_nil, toSmooth_representation,
    smoothRepresentation_apply]

/-- Averaging against a compact weight is equivariant for left translation
of the weight and the original orthogonal action on smooth vectors. -/
def orthogonalSmoothAverage (v : D[R]) :
    Representation.IntertwiningMap (A := ℂ) (V := C(K, ℂ)) (W := D[R])
      (leftRegular : Representation ℂ K C(K, ℂ))
      ((representation I R).comp (Unitary.toUnits : K →* G)) where
  toLinearMap :=
    { toFun := fun κ => compactSmoothAverage R hR μ orthogonalInclusion κ v
      map_add' := by
        intro κ w
        apply injective_emptyWord R
        rw [map_add]
        simp only [derivativeCLM_nil_compactSmoothAverage, compactWeightedOrbit_apply,
          ContinuousMap.add_apply, add_smul]
        exact integral_add
          (integrable_compactWeightedOrbit μ R hR orthogonalInclusion κ _)
          (integrable_compactWeightedOrbit μ R hR orthogonalInclusion w _)
      map_smul' := by
        intro c κ
        apply injective_emptyWord R
        rw [map_smul]
        simp only [derivativeCLM_nil_compactSmoothAverage, compactWeightedOrbit_apply,
          ContinuousMap.smul_apply, RingHom.id_apply, smul_assoc, integral_smul] }
  isIntertwining' k := by
    apply LinearMap.ext
    intro κ
    apply injective_emptyWord R
    change derivativeCLM I R []
        (compactSmoothAverage R hR μ orthogonalInclusion (leftRegular k κ) v) =
      derivativeCLM I R [] (representation I R (Unitary.toUnits k)
        (compactSmoothAverage R hR μ orthogonalInclusion κ v))
    simp only [derivativeCLM_nil_representation, derivativeCLM_nil_compactSmoothAverage,
      compactWeightedOrbit_apply]
    let b := derivativeCLM I R [] v
    have hi := integrable_compactWeightedOrbit μ R hR orthogonalInclusion κ b
    rw [← (R (Unitary.toUnits k)).integral_comp_comm hi]
    calc
      _ = ∫ x, κ x • R (Unitary.toUnits (k * x)) b ∂μ := by
        rw [← integral_mul_left_eq_self
          (fun x => leftRegular k κ x • R (orthogonalInclusion x) b) k]
        simp only [leftRegular_apply, inv_mul_cancel_left, orthogonalInclusion,
          ContinuousMap.coe_mk]
      _ = _ := by
        simp only [map_mul, mul_apply_eq_comp, map_smul, orthogonalInclusion,
          ContinuousMap.coe_mk]

@[simp]
theorem orthogonalSmoothAverage_apply (v : D[R]) (κ : C(K, ℂ)) :
    orthogonalSmoothAverage R hR μ v κ = compactSmoothAverage R hR μ orthogonalInclusion κ v :=
  rfl

/-- Finite left-orbit weights produce compact-finite smooth integrals. -/
theorem orthogonalSmoothAverage_mem_smoothKFinite (v : D[R]) {κ : C(K, ℂ)}
    (hκ : κ ∈ finiteWeights) :
    orthogonalSmoothAverage R hR μ v κ ∈ smoothKFinite ℝ n R :=
  (show FiniteVectors.IsFiniteVector leftRegular κ from hκ).map
    (orthogonalSmoothAverage R hR μ v)

include hR μ in
set_option maxHeartbeats 600000 in
/-- Compact-finite smooth vectors are dense for all genuine word derivatives. -/
theorem dense_smoothKFinite_of_orthogonalHaar :
    Dense (smoothKFinite ℝ n (E := E) R : Set D[R]) := by
  let S := (smoothKFinite ℝ n R).topologicalClosure
  intro v
  change v ∈ S
  by_contra hv
  have hS : IsClosed (S : Set D[R]) := (smoothKFinite ℝ n R).isClosed_topologicalClosure
  obtain ⟨L, c, hLs, hvL⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (S.restrictScalars ℝ).convex hS hv
  have hL (z : D[R]) (hz : z ∈ S) : L z = 0 := by
    by_contra hn
    let d : ℂ := ((c + 1 : ℝ) : ℂ)
    have h := hLs ((d / L z) • z) (S.smul_mem _ hz)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at h
    change c + 1 < c at h
    linarith
  let F : C(K, ℂ) :=
    ⟨fun k => L (representation I R (Unitary.toUnits k) v),
      L.continuous.comp ((continuous_representation_units R hR).comp
        (continuous_unitary_toUnits.prodMk continuous_const))⟩
  have hF : ∀ κ ∈ polynomialStar n, ∫ k, κ k * F k ∂μ = 0 := by
    intro κ hκ
    have ha := apply_compactSmoothAverage R hR μ orthogonalInclusion κ v L
    change L (orthogonalSmoothAverage R hR μ v κ) = ∫ k, κ k * F k ∂μ at ha
    rw [← ha]
    apply hL
    apply Submodule.le_topologicalClosure
    exact orthogonalSmoothAverage_mem_smoothKFinite R hR μ v (polynomial_le_finiteWeights hκ)
  have hzero := congrArg (fun f : C(K, ℂ) => f 1)
    (eq_zero_of_integral_polynomial_mul_eq_zero μ F hF)
  change L (representation I R (Unitary.toUnits (1 : K)) v) = 0 at hzero
  simp only [map_one, Module.End.one_apply] at hzero
  rw [hzero] at hvL
  have hc := hLs 0 (S.zero_mem)
  simp only [map_zero] at hc hvL
  exact (lt_asymm hc hvL)

/-- Density in the genuine smooth topology for any jointly continuous real
general linear group representation on a complex Banach space. -/
def RealSmoothCompactFiniteDensityStatement : Prop :=
  ∀ (m : ℕ) (B : Type u) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (P : Langlands.GeneralLinear m ℝ →* (B →L[ℂ] B)),
    IsContinuousRepresentation P →
      Dense (smoothKFinite ℝ m P : Set (DerivativeSmoothVectors (matrixModel ℝ m) P))

theorem realSmoothCompactFiniteDensity : RealSmoothCompactFiniteDensityStatement.{u} := by
  intro m B _ _ _ P hP
  exact dense_smoothKFinite_of_orthogonalHaar P hP (Measure.haar : Measure
    (Matrix.unitaryGroup (Fin m) ℝ))

end Langlands.Archimedean.DerivativeSmoothVectors
