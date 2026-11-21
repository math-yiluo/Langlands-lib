import Langlands.Representation.Archimedean.RealFrobeniusCompactRecovery
import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness
import Langlands.Representation.Archimedean.SmoothUnitAction

/-! # Density of the real Frobenius image in the derivative topology -/

noncomputable section

open Filter MeasureTheory
open scoped Topology Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open OrthogonalFinitePolynomial RealPrincipalSeriesDuality DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] OrthogonalFinitePolynomial.secondCountableTopology_orthogonal
attribute [local instance] measurableSpaceK borelSpaceK

private theorem mem_closure_of_finite_restrictions {ι E : Type*} [TopologicalSpace E]
    {S : Set (ι → E)} {x : ι → E}
    (h : ∀ t : Finset ι, (fun i : t => x i) ∈ closure ((fun (f : ι → E) (i : t) => f i) '' S)) :
    x ∈ closure S := by
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨t, B, hB, hBU⟩ := Filter.mem_pi'.mp hU
  let B' : Set (t → E) := Set.pi Set.univ (fun i => B i)
  have hB' : B' ∈ 𝓝 (fun i : t => x i) := by
    rw [nhds_pi]
    exact Filter.pi_mem_pi (Set.toFinite _) (fun i _ => hB i)
  obtain ⟨_, hf, f, hfS, rfl⟩ := mem_closure_iff_nhds.mp (h t) B' hB'
  exact ⟨f, hBU (fun i hi => hf (⟨i, hi⟩ : t) (Set.mem_univ _)), hfS⟩

private def finiteRestriction {ι E : Type*} [AddCommGroup E] [Module ℂ E] (t : Finset ι) :
    (ι → E) →ₗ[ℂ] (t → E) :=
  LinearMap.pi fun i => LinearMap.proj i.val

section Integrals

variable {n : ℕ} {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

private def finiteProfile (f : C(O, ι → E)) (t : Finset ι) : C(O, t → E) :=
  ⟨fun k => finiteRestriction t (f k), continuous_pi fun i => (continuous_apply i.val).comp f.continuous⟩

private theorem integral_finiteProfile (f : C(O, ι → E)) (φ : C(O, ℂ)) (t : Finset ι) :
    (∫ k, φ k • finiteProfile f t k ∂haarOrthogonal n) =
      finiteRestriction t (fun w => ∫ k, φ k • f k w ∂haarOrthogonal n) := by
  funext i
  have hI := OrthogonalFinitePolynomial.integrable_of_continuous (haarOrthogonal n)
    (φ.continuous.smul (finiteProfile f t).continuous)
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : t => E) i).integral_comp_comm hI).symm

end Integrals

section SmoothAverages

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local notation "O" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "I" => matrixModel ℝ n
local notation "GL" => Langlands.GeneralLinear n ℝ

variable (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)

private def compactDerivativeProfile (v : DerivativeSmoothVectors I R) : C(O, List Mat → E) := by
  have hu : Continuous (Unitary.toUnits : O → GL) :=
    continuous_subtype_val.comp (continuous_orthogonalCompactEquiv (n := n))
  have hA : Continuous (fun p : GL × DerivativeSmoothVectors I R =>
      DerivativeSmoothVectors.representation I R p.1 p.2) :=
    continuous_representation_units R hR
  exact ⟨fun k => derivativeCoordinates I R (DerivativeSmoothVectors.representation I R
      (Unitary.toUnits k) v), (isEmbedding_derivativeCoordinates I R).continuous.comp
        (hA.comp (hu.prodMk continuous_const))⟩

private theorem exists_smooth_compact_integral (v : DerivativeSmoothVectors I R) (φ : C(O, ℂ)) :
    ∃ y : DerivativeSmoothVectors I R, derivativeCoordinates I R y =
      fun s => ∫ k, φ k • compactDerivativeProfile R hR v k s ∂haarOrthogonal n := by
  let f := compactDerivativeProfile R hR v
  let c := derivativeCoordinates I R
  have hc : IsClosed (Set.range c) := isClosed_range_derivativeCoordinates_units R hR
  change (fun s => ∫ k, φ k • f k s ∂haarOrthogonal n) ∈ Set.range c
  rw [← hc.closure_eq]
  apply mem_closure_of_finite_restrictions
  intro t
  let P := (LinearMap.range c).map (finiteRestriction t)
  change finiteRestriction t (fun s => ∫ k, φ k • f k s ∂haarOrthogonal n) ∈
    closure (P : Set (t → E))
  rw [← integral_finiteProfile]
  change (∫ k, φ k • finiteProfile f t k ∂haarOrthogonal n) ∈ P.topologicalClosure
  have hmem (k : O) : finiteProfile f t k ∈ P :=
    ⟨c (DerivativeSmoothVectors.representation I R (Unitary.toUnits k) v),
      ⟨_, rfl⟩, rfl⟩
  exact (P.topologicalClosure.restrictScalars ℝ).convex.integral_mem P.isClosed_topologicalClosure
    (Eventually.of_forall fun k => P.topologicalClosure.smul_mem (φ k)
      (P.le_topologicalClosure (hmem k)))
    (OrthogonalFinitePolynomial.integrable_of_continuous (haarOrthogonal n)
      (φ.continuous.smul (finiteProfile f t).continuous))

/-- The smooth vector obtained by integrating each Lie-word coordinate of a
continuously weighted orthogonal orbit. -/
def compactSmoothAverage (v : DerivativeSmoothVectors I R) (φ : C(O, ℂ)) :
    DerivativeSmoothVectors I R :=
  (exists_smooth_compact_integral R hR v φ).choose

private theorem derivativeCoordinates_compactSmoothAverage
    (v : DerivativeSmoothVectors I R) (φ : C(O, ℂ)) :
    derivativeCoordinates I R (compactSmoothAverage R hR v φ) =
      fun s => ∫ k, φ k • compactDerivativeProfile R hR v k s ∂haarOrthogonal n :=
  (exists_smooth_compact_integral R hR v φ).choose_spec

omit [CompleteSpace E] in
private theorem compactDerivativeProfile_one (v : DerivativeSmoothVectors I R) :
    compactDerivativeProfile R hR v 1 = derivativeCoordinates I R v := by
  change derivativeCoordinates I R (DerivativeSmoothVectors.representation I R
    (Unitary.toUnits (1 : O)) v) = _
  simp

private theorem integral_compactDerivativeProfile_nil {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']
    (v : DerivativeSmoothVectors I R) (φ : C(O, ℂ)) (j : E →L[ℂ] E') :
    j (∫ k, φ k • compactDerivativeProfile R hR v k [] ∂haarOrthogonal n) =
      ∫ k, φ k • j (R (Unitary.toUnits k) (toSmooth I R v)) ∂haarOrthogonal n := by
  let f := compactDerivativeProfile R hR v
  have hC : Continuous (fun k => φ k • f k []) :=
    φ.continuous.smul ((continuous_apply []).comp f.continuous)
  have hI := OrthogonalFinitePolynomial.integrable_of_continuous (haarOrthogonal n) hC
  have hnil (k : O) : f k [] = R (Unitary.toUnits k) (toSmooth I R v) := by
    change derivativeCoordinates I R (DerivativeSmoothVectors.representation I R
      (Unitary.toUnits k) v) [] = _
    rw [derivativeCoordinates_apply, iteratedLieDerivative_nil, toSmooth_representation,
      smoothRepresentation_apply]
  change j (∫ k, φ k • f k [] ∂haarOrthogonal n) = _
  simpa only [map_smul, hnil] using (j.integral_comp_comm hI).symm

include hR in
private theorem denseRange_of_polynomial_averages {V E' : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']
    (L : V →ₗ[ℂ] DerivativeSmoothVectors I R) (j : E →L[ℂ] E') (hj : Function.Injective j)
    (h : ∀ (v : DerivativeSmoothVectors I R) (φ : C(O, ℂ)), φ ∈ polynomialStar n →
      ∃ w : V, j (toSmooth I R (L w)) =
        ∫ k, φ k • j (R (Unitary.toUnits k) (toSmooth I R v)) ∂haarOrthogonal n) :
    DenseRange L := by
  let c := derivativeCoordinates I R
  let B := c.comp L
  intro v
  rw [(isEmbedding_derivativeCoordinates I R).closure_eq_preimage_closure_image]
  change c v ∈ closure (c '' Set.range L)
  rw [← Set.range_comp]
  change c v ∈ closure (Set.range B)
  apply mem_closure_of_finite_restrictions
  intro t
  let f := compactDerivativeProfile R hR v
  let P := (LinearMap.range B).map (finiteRestriction t)
  change finiteRestriction t (c v) ∈ P.topologicalClosure
  have havg (φ : C(O, ℂ)) (hφ : φ ∈ polynomialStar n) :
      (∫ k, φ k • finiteProfile f t k ∂haarOrthogonal n) ∈ P.topologicalClosure := by
    let z := compactSmoothAverage R hR v φ
    have hz : c z = fun s => ∫ k, φ k • f k s ∂haarOrthogonal n :=
      derivativeCoordinates_compactSmoothAverage R hR v φ
    obtain ⟨w, hw⟩ := h v φ hφ
    have hl : z = L w := by
      apply (toSmooth I R).injective
      apply Subtype.ext
      apply hj
      calc
        _ = j (∫ k, φ k • f k [] ∂haarOrthogonal n) := congrArg j (congrFun hz [])
        _ = _ := (integral_compactDerivativeProfile_nil R hR v φ j).trans hw.symm
    rw [integral_finiteProfile, ← hz, hl]
    exact P.le_topologicalClosure ⟨B w, ⟨w, rfl⟩, rfl⟩
  have hmem := mem_closedSubmodule_of_polynomial_integrals_mem (E := t → E)
    (haarOrthogonal n) (finiteProfile f t) P.isClosed_topologicalClosure havg 1
  change finiteRestriction t (f 1) ∈ P.topologicalClosure at hmem
  rw [show f 1 = c v from compactDerivativeProfile_one R hR v] at hmem
  exact hmem

end SmoothAverages

section FrobeniusDensity

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)

local notation "I" => matrixModel ℝ n
local notation "W" => (frobeniusClosure hgk hℓ : Type)
local notation "R" => frobeniusClosureRepresentation hgk hℓ

set_option maxHeartbeats 800000 in
/-- The algebraic Frobenius map is dense in the genuine word-derivative topology
of the smooth vectors of its Hilbert closure. -/
theorem denseRange_frobeniusSmoothMap : DenseRange (frobeniusSmoothMap hgk hℓ) := by
  let j : W →L[ℂ] Hilbert a e := (frobeniusClosure hgk hℓ).subtypeL
  have hj : Function.Injective j := fun _ _ h => Subtype.ext h
  let L : V →ₗ[ℂ] DerivativeSmoothVectors I (E := W) R := frobeniusSmoothMap hgk hℓ
  have hR : IsContinuousRepresentation (E := W) R :=
    isContinuousRepresentation_frobeniusClosureRepresentation hgk hℓ
  have hW : CompleteSpace W := (isClosed_frobeniusClosure hgk hℓ).isComplete.completeSpace_coe
  have hH : CompleteSpace (Hilbert a e) := inferInstance
  change DenseRange L
  let densityOnClosure := @denseRange_of_polynomial_averages n W
    (Submodule.normedAddCommGroup (frobeniusClosure hgk hℓ))
    (Submodule.normedSpace (frobeniusClosure hgk hℓ)) hW
  let densityForRepresentation := @densityOnClosure R hR
  let densityInAmbientSpace := @densityForRepresentation V (Hilbert a e) ‹AddCommGroup V› ‹Module ℂ V›
    (Submodule.normedAddCommGroup (closureSubmodule a e))
    (Submodule.normedSpace (closureSubmodule a e)) hH
  let density := densityInAmbientSpace L j hj
  apply density
  intro v φ hφ
  let x : W := toSmooth I (E := W) R v
  obtain ⟨w, hw⟩ := orthogonalAverage_mem_frobeniusRange hgk hℓ hφ x.2
  refine ⟨w, ?_⟩
  change (frobeniusClosure hgk hℓ).subtypeL
    (toSmooth I (E := W) R (frobeniusSmoothMap hgk hℓ w)) =
      ∫ k, φ k • (frobeniusClosure hgk hℓ).subtypeL (R (Unitary.toUnits k) x) ∂haarOrthogonal n
  simp only [Submodule.subtypeL_apply, coe_toSmooth_frobeniusSmoothMap, coe_frobeniusClosureMap,
    coe_frobeniusClosureRepresentation]
  exact hw.trans (orthogonalAverage_apply a e φ x.1)

end FrobeniusDensity
end Langlands.Archimedean.RealPrincipalSeriesHilbert
