import Langlands.Global.RankinSelberg.RealSmoothWhittakerEvaluation
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Finite separation of compactly averaged real Whittaker coefficients -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.CompactRepresentativeWeights MeasureTheory Set
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "K" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation "E" ds => Carrier (r + 1) ds
local notation "S" ds => realStandardModule (r + 1) ds
local notation "V" ds => Automorphic.realStandardKFinite (r + 1) ds
local notation "R" ds => representation (n := r + 1) ds
local notation "D" ds => DerivativeSmoothVectors I (R ds)
local notation "P" ds => principalSeries ℝ (r + 1) (realPositionCharacter (RealPrincipalSeries.expand ds))

private def compactInclusion : C(K, G) :=
  ⟨Unitary.toUnits, continuous_unitary_toUnits⟩

private theorem exists_finiteConvolutionRange (ν : Measure K) [ν.IsHaarMeasure]
    (κ : C(K, ℂ)) (hκ : κ ∈ finiteWeights) :
    ∃ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W ∧
      ∀ φ : C(K, ℂ), (fun x => ∫ y, κ (x⁻¹ * y) * φ y ∂ν) ∈ W := by
  classical
  let Q := FiniteVectors.orbitSpan leftRegular κ
  let : FiniteDimensional ℂ Q := hκ
  let b := Module.finBasis ℂ Q
  let c (i : Fin (Module.finrank ℂ Q)) (x : K) :=
    b.repr ⟨leftRegular x κ, FiniteVectors.action_mem_orbitSpan leftRegular x κ⟩ i
  have h (x y : K) : κ (x⁻¹ * y) = ∑ i, c i x * (b i).val y := by
    have he := congrArg (fun z : Q => z.val y)
      (b.sum_repr ⟨leftRegular x κ, FiniteVectors.action_mem_orbitSpan leftRegular x κ⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul, leftRegular_apply, c] using he.symm
  refine ⟨Submodule.span ℂ (range c), FiniteDimensional.span_of_finite ℂ (finite_range c), ?_⟩
  intro φ
  have he : (fun x => ∫ y, κ (x⁻¹ * y) * φ y ∂ν) =
      ∑ i, (∫ y, (b i).val y * φ y ∂ν) • c i := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h, Finset.sum_mul]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [← integral_mul_const]
      apply integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      ring
    · intro i _
      exact OrthogonalFinitePolynomial.integrable_of_continuous ν
        ((continuous_const.mul (b i).val.continuous).mul φ.continuous)
  rw [he]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))

private theorem average_compactProfile (ds : List RealBlock)
    (ν : Measure K) [ν.IsHaarMeasure] (κ : C(K, ℂ)) (v : E ds) (x : K) :
    (compactWeightedOrbit ν (R ds) (isContinuousRepresentation ds)
        compactInclusion κ v).val x =
      ∫ y, κ (x⁻¹ * y) * v.val y ∂ν := by
  let Q := profileEval ds x
  change Q (compactWeightedOrbit ν (R ds) (isContinuousRepresentation ds) compactInclusion κ v) = _
  rw [compactWeightedOrbit_apply, ← Q.integral_comp_comm
    (integrable_compactWeightedOrbit ν (R ds) (isContinuousRepresentation ds) compactInclusion κ v)]
  rw [← integral_mul_left_eq_self (fun y : K => κ (x⁻¹ * y) * v.val y) x]
  apply integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  change Q (κ k • (R ds) (Unitary.toUnits k) v) = κ (x⁻¹ * (x * k)) * v.val (x * k)
  rw [map_smul, profileEval_apply, representation_apply, ← map_mul,
    extensionOfProfile_compact, inv_mul_cancel_left, smul_eq_mul]

private theorem injective_emptyDerivative (ds : List RealBlock) :
    Function.Injective (derivativeCLM I (R ds) []) := by
  intro u v h
  apply (toSmooth I (R ds)).injective
  apply Subtype.ext
  simpa only [derivativeCLM_apply, iteratedLieDerivative_nil] using h

set_option maxHeartbeats 600000 in
private theorem finiteDimensional_range_compactAverage (ds : List RealBlock)
    (ν : Measure K) [ν.IsHaarMeasure] (κ : C(K, ℂ)) (hκ : κ ∈ finiteWeights) :
    FiniteDimensional ℂ (compactWeightedOrbit ν (R ds) (isContinuousRepresentation ds)
      compactInclusion κ).toLinearMap.range := by
  let T := compactWeightedOrbit ν (R ds) (isContinuousRepresentation ds) compactInclusion κ
  obtain ⟨H, hH, hConvol⟩ := exists_finiteConvolutionRange ν κ hκ
  let j : (E ds) →ₗ[ℂ] (K → ℂ) :=
    (ContinuousMap.coeFnLinearMap ℂ).comp (closureSubmodule ds).subtype
  have hj : Function.Injective j := fun v w he => Subtype.ext (ContinuousMap.ext (congrFun he))
  let A : T.toLinearMap.range →ₗ[ℂ] H :=
    (j.comp T.toLinearMap.range.subtype).codRestrict H (fun w => by
      obtain ⟨v, hv⟩ := w.property
      change j w.val ∈ H
      rw [← hv]
      change j (T v) ∈ H
      have he : j (T v) = fun x => ∫ y, κ (x⁻¹ * y) * v.val y ∂ν :=
        funext (average_compactProfile ds ν κ v)
      rw [he]
      exact hConvol v.val)
  let : FiniteDimensional ℂ H := hH
  exact Module.Finite.of_injective A (fun v w e =>
    Subtype.ext (hj (congrArg (fun x : H => x.val) e)))

set_option maxHeartbeats 800000 in
private theorem exists_orthogonalProjection_coordinates (ds : List RealBlock)
    (ν : Measure K) [ν.IsHaarMeasure] (κ : C(K, ℂ)) (hκ : κ ∈ finiteWeights) :
    ∃ (m : ℕ) (u : Fin m → V ds) (L : Fin m → (D ds) →L[ℂ] ℂ),
      ∀ v, orthogonalSmoothAverage (R ds) (isContinuousRepresentation ds) ν v κ =
        ∑ i, L i v • (compactFiniteEquiv ds (u i)).val := by
  classical
  let hR := isContinuousRepresentation (n := r + 1) ds
  let q := derivativeCLM I (R ds) []
  let T := compactWeightedOrbit ν (R ds) hR compactInclusion κ
  let C := T.comp q
  let W := C.toLinearMap.range
  let : FiniteDimensional ℂ T.toLinearMap.range := finiteDimensional_range_compactAverage ds ν κ hκ
  have hle : W ≤ T.toLinearMap.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨q v, rfl⟩
  let : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hle
  let m := Module.finrank ℂ W
  let b := Module.finBasis ℂ W
  choose v hv using fun i : Fin m => (b i).property
  have hmem (i : Fin m) : orthogonalSmoothAverage (R ds) hR ν (v i) κ ∈
      smoothKFinite ℝ (r + 1) (R ds) :=
    orthogonalSmoothAverage_mem_smoothKFinite (R ds) hR ν (v i) hκ
  let u (i : Fin m) : V ds := (compactFiniteEquiv ds).symm ⟨_, hmem i⟩
  have hu (i : Fin m) : (compactFiniteEquiv ds (u i)).val =
      orthogonalSmoothAverage (R ds) hR ν (v i) κ := by
    simp only [u, LinearEquiv.apply_symm_apply]
  have hAvg (w : D ds) : q (orthogonalSmoothAverage (R ds) hR ν w κ) = C w :=
    derivativeCLM_nil_compactSmoothAverage (R ds) hR ν compactInclusion κ w
  let c (i : Fin m) : W →L[ℂ] ℂ := (b.coord i).toContinuousLinearMap
  choose forms hForms _hNorm using fun i : Fin m => exists_extension_norm_eq W (c i)
  refine ⟨m, u, fun i => (forms i).comp C, fun w => ?_⟩
  let w' : W := ⟨C w, ⟨w, rfl⟩⟩
  apply injective_emptyDerivative ds
  change q (orthogonalSmoothAverage (R ds) hR ν w κ) =
    q (∑ i, forms i (C w) • (compactFiniteEquiv ds (u i)).val)
  simp only [hAvg, map_sum, map_smul, hu]
  have he (i : Fin m) : forms i (C w) = b.repr w' i := hForms i w'
  have hv' (i : Fin m) : C (v i) = (b i).val := hv i
  simp only [he, hv']
  have h := congrArg (fun z : W => z.val) (b.sum_repr w')
  simpa only [Submodule.coe_sum, Submodule.coe_smul, w'] using h.symm

set_option maxHeartbeats 600000 in
/-- The original compact-finite Whittaker factor and a bounded matrix coefficient
factor separate a compact average with a finite left-orbit weight. -/
theorem exists_compactProjection_coefficients (ds : List RealBlock) (a : ℝˣ)
    (B : (V ds) →ₗ[ℂ] (G → ℂ)) (L : (D ds) →L[ℂ] ℂ)
    (hL : IsWhittakerStandardEvaluation ds a B L)
    (ν : Measure K) [ν.IsHaarMeasure] (κ : C(K, ℂ)) (hκ : κ ∈ finiteWeights) :
    ∃ (m : ℕ) (u : Fin m → V ds) (ℓ : Fin m → (P ds) →ₗ[ℂ] ℂ),
      (∀ i, RealPrincipalSeries.HasCompactDerivativeBound r (RealPrincipalSeries.expand ds) (ℓ i)) ∧
      ∀ (f : V ds) (x g : G),
        (∫ k, κ k * B f (x * Unitary.toUnits k * g) ∂ν) =
          ∑ i, B (u i) x * ℓ i (RealPrincipalSeries.translate r (RealPrincipalSeries.expand ds) g
            (RealPrincipalSeries.expandedSmoothInclusion r ds f)) := by
  classical
  let hR := isContinuousRepresentation (n := r + 1) ds
  obtain ⟨d, u, L₀, hCoords⟩ := exists_orthogonalProjection_coordinates ds ν κ hκ
  choose ℓ hℓ hExt using fun i : Fin d => exists_bound_extension ds (L₀ i)
  refine ⟨d, u, ℓ, hℓ, fun f x g => ?_⟩
  let v := DerivativeSmoothVectors.representation I (R ds) g (compactFiniteEquiv ds f).val
  let Lx := L.comp (SmoothAction.derivativeAction I (R ds) x)
  have hInt : (∫ k, κ k * B f (x * Unitary.toUnits k * g) ∂ν) =
      Lx (orthogonalSmoothAverage (R ds) hR ν v κ) := by
    change _ = Lx (compactSmoothAverage (R ds) hR ν compactInclusion κ v)
    rw [apply_compactSmoothAverage]
    apply integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    change κ k * B f (x * Unitary.toUnits k * g) = κ k *
      L (DerivativeSmoothVectors.representation I (R ds) x
        (DerivativeSmoothVectors.representation I (R ds) (Unitary.toUnits k)
          (DerivativeSmoothVectors.representation I (R ds) g (compactFiniteEquiv ds f).val)))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hL.1]
  have hBasis (i : Fin d) : Lx (compactFiniteEquiv ds (u i)).val = B (u i) x := by
    change L (DerivativeSmoothVectors.representation I (R ds) x
      (compactFiniteEquiv ds (u i)).val) = B (u i) x
    exact hL.1 (u i) x
  have hRepr (i : Fin d) : ℓ i (RealPrincipalSeries.translate r (RealPrincipalSeries.expand ds) g
        (RealPrincipalSeries.expandedSmoothInclusion r ds f)) = L₀ i v := by
    let f₀ : S ds := ⟨f.val, f.property.1⟩
    have he : RealPrincipalSeries.translate r (RealPrincipalSeries.expand ds) g
          (RealPrincipalSeries.expandedSmoothInclusion r ds f) =
        expandedStandardInclusion ds (translate ds g f₀) := Subtype.ext rfl
    calc
      _ = ℓ i (expandedStandardInclusion ds (translate ds g f₀)) := congrArg (ℓ i) he
      _ = L₀ i (derivativeEquiv ds (translate ds g f₀)) := hExt i _
      _ = _ := congrArg (L₀ i) (derivativeEquiv_translate ds g f₀)
  calc
    _ = Lx (orthogonalSmoothAverage (R ds) hR ν v κ) := hInt
    _ = Lx (∑ i, L₀ i v • (compactFiniteEquiv ds (u i)).val) :=
      congrArg Lx (hCoords v)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hBasis, hRepr, smul_eq_mul, mul_comm]

variable (r) in
/-- The smooth realization of a coefficient map gives a separated compact
average with matrix coefficient factors of the expanded position model. -/
def RealWhittakerCompactProjectionStatement : Prop :=
  ∀ (ds : List RealBlock) (a : ℝˣ) (B : (V ds) →ₗ[ℂ] (G → ℂ))
    (L : (D ds) →L[ℂ] ℂ),
    IsWhittakerStandardEvaluation ds a B L →
  ∀ (ν : Measure K) [ν.IsHaarMeasure] (κ : C(K, ℂ)), κ ∈ finiteWeights →
    ∃ (m : ℕ) (u : Fin m → V ds) (ℓ : Fin m → (P ds) →ₗ[ℂ] ℂ),
      (∀ i, RealPrincipalSeries.HasCompactDerivativeBound r (RealPrincipalSeries.expand ds) (ℓ i)) ∧
      ∀ (f : V ds) (x g : G),
        (∫ k, κ k * B f (x * Unitary.toUnits k * g) ∂ν) =
          ∑ i, B (u i) x * ℓ i (RealPrincipalSeries.translate r (RealPrincipalSeries.expand ds) g
            (RealPrincipalSeries.expandedSmoothInclusion r ds f))

theorem realWhittakerCompactProjection : RealWhittakerCompactProjectionStatement r :=
  fun ds a B L hL ν _ κ hκ => exists_compactProjection_coefficients ds a B L hL ν κ hκ

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
