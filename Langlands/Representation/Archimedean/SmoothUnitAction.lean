import Langlands.Representation.Archimedean.SmoothDerivativeBasisTopology
import Langlands.Representation.Archimedean.SmoothHilbert
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-! # Joint continuity of the genuine smooth-vector action -/

noncomputable section

open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Conjugation by the inverse of a unit, as a continuous real linear map on the algebra. -/
def inverseConjugationCLM (g : Aˣ) : A →L[ℝ] A :=
  ContinuousLinearMap.mulLeftRight ℝ A (g⁻¹ : Aˣ).val g.val

@[simp]
theorem inverseConjugationCLM_apply (g : Aˣ) (X : A) :
    inverseConjugationCLM g X = (g⁻¹ : Aˣ).val * X * g.val :=
  rfl

theorem norm_inverseConjugationCLM_le (g : Aˣ) :
    ‖inverseConjugationCLM g‖ ≤ ‖(g⁻¹ : Aˣ).val‖ * ‖g.val‖ :=
  ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ A _ _

private theorem continuous_inverseConjugationCLM_apply (X : A) :
    Continuous (fun g : Aˣ => inverseConjugationCLM g X) := by
  simp only [inverseConjugationCLM_apply]
  exact (Units.continuous_coe_inv.mul continuous_const).mul Units.continuous_val

variable [CompleteSpace A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R

private theorem mfderiv_inverseConjugation_units (g : Aˣ) :
    mfderiv 𝓜 𝓜 (fun h : Aˣ => g⁻¹ * h * g) 1 = inverseConjugationCLM g := by
  let f := fun h : Aˣ => g⁻¹ * h * g
  have hf : ContMDiff 𝓜 𝓜 ∞ f := (contMDiff_const.mul contMDiff_id).mul contMDiff_const
  have hv : ContMDiff 𝓜 𝓜 ∞ (Units.val : Aˣ → A) := Units.contMDiff_val
  have hval (h : Aˣ) : mfderiv 𝓜 𝓜 (Units.val : Aˣ → A) h = ContinuousLinearMap.id ℝ A :=
    mfderiv_extChartAt_self (I := 𝓜) (x := h)
  have h₁ := mfderiv_comp (1 : Aˣ) (hv.mdifferentiableAt (by simp) (x := f 1))
    (hf.mdifferentiableAt (by simp))
  have h₂ := mfderiv_comp (1 : Aˣ) (inverseConjugationCLM g).differentiableAt.mdifferentiableAt
    (hv.mdifferentiableAt (by simp))
  have he : (Units.val : Aˣ → A) ∘ f = (inverseConjugationCLM g) ∘ Units.val := rfl
  rw [he, h₂, hval, hval, ContinuousLinearMap.mfderiv_eq] at h₁
  change (inverseConjugationCLM g).comp (ContinuousLinearMap.id ℝ A) =
    (ContinuousLinearMap.id ℝ A).comp (mfderiv 𝓜 𝓜 f 1) at h₁
  rwa [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, eq_comm] at h₁

private theorem lieDerivative_apply_units (g : Aˣ) (X : A) {v : E}
    (hv : IsSmoothVector 𝓜 R v) :
    lieDerivative 𝓜 R X (R g v) = R g (lieDerivative 𝓜 R (inverseConjugationCLM g X) v) := by
  let f := fun h : Aˣ => g⁻¹ * h * g
  let T := (R g).restrictScalars ℝ
  have hf : ContMDiff 𝓜 𝓜 ∞ f := (contMDiff_const.mul contMDiff_id).mul contMDiff_const
  have hf1 : f 1 = 1 := by simp [f]
  have he : orbitMap R (R g v) = T ∘ (orbitMap R v ∘ f) := by
    funext h
    change R h (R g v) = R g (R (g⁻¹ * h * g) v)
    simp only [← mul_apply_eq_comp, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  have h₁ := mfderiv_comp (1 : Aˣ) T.differentiableAt.mdifferentiableAt
    ((hv.comp hf).mdifferentiableAt (by simp))
  have h₂ := mfderiv_comp (1 : Aˣ) (hv.mdifferentiableAt (by simp) (x := f 1))
    (hf.mdifferentiableAt (by simp))
  unfold lieDerivative
  rw [he, h₁, h₂, ContinuousLinearMap.mfderiv_eq, hf1,
    mfderiv_inverseConjugation_units]
  rfl

/-- Differentiation of a translated smooth vector conjugates its direction by the inverse unit. -/
theorem operator_representation_units (g : Aˣ) (X : A) (v : D) :
    operator 𝓜 R X (representation 𝓜 R g v) =
      representation 𝓜 R g (operator 𝓜 R (inverseConjugationCLM g X) v) := by
  apply (toSmooth 𝓜 R).injective
  apply Subtype.ext
  exact lieDerivative_apply_units R g X (toSmooth 𝓜 R v).property

/-- Word-coordinate covariance for the actual action of units. -/
theorem derivativeCoordinates_representation_units (s : List A) (g : Aˣ) (v : D) :
    derivativeCoordinates 𝓜 R (representation 𝓜 R g v) s =
      R g (derivativeCoordinates 𝓜 R v (s.map (inverseConjugationCLM g))) := by
  induction s using List.reverseRecOn generalizing v with
  | nil => rfl
  | append_singleton s X ih =>
      rw [List.map_append, List.map_singleton, ← derivativeCoordinates_operator,
        operator_representation_units, ih, derivativeCoordinates_operator]

/-- Basis expansion of the genuine derivative, as an identity in the smooth carrier. -/
theorem operator_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A)
    (X : A) (v : D) :
    operator 𝓜 R X v = ∑ i, b.coord i X • operator 𝓜 R (b i) v := by
  let T : A →ₗ[ℝ] smoothVectors 𝓜 R :=
    ((LinearMap.applyₗ (toSmooth 𝓜 R v)).restrictScalars ℝ).comp (smoothLieDerivativeDirection 𝓜 R)
  have h := congrArg T (b.sum_repr X)
  apply (toSmooth 𝓜 R).injective
  let e := (toSmooth 𝓜 R).toLinearMap.restrictScalars ℝ
  change T X = e (∑ i, b.coord i X • operator 𝓜 R (b i) v)
  rw [map_sum]
  simp_rw [map_smul]
  change T X = ∑ i, b.coord i X • T (b i)
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using h.symm

variable [FiniteDimensional ℝ A]

/-- Differentiating a smooth vector is jointly continuous in its Lie direction and vector. -/
theorem continuous_operator_uncurry : Continuous (fun p : A × D => operator 𝓜 R p.1 p.2) := by
  let b := Module.finBasis ℝ A
  have he (p : A × D) : operator 𝓜 R p.1 p.2 = ∑ i, b.coord i p.1 • operator 𝓜 R (b i) p.2 :=
    operator_eq_sum_basis R b p.1 p.2
  simp_rw [he]
  apply continuous_finsetSum
  intro i _
  exact Continuous.smul (M := ℝ)
    ((b.coord i).toContinuousLinearMap.continuous.comp continuous_fst)
    ((operatorCLM 𝓜 R (b i)).continuous.comp continuous_snd)

/-- The actual action on smooth vectors is jointly continuous in the genuine word topology. -/
theorem continuous_representation_units (hR : IsContinuousRepresentation R) :
    Continuous (fun p : Aˣ × D => representation 𝓜 R p.1 p.2) := by
  have hcoord (s : List A) (f : Aˣ × D → D) (hf : Continuous f) :
      Continuous (fun p : Aˣ × D =>
        derivativeCoordinates 𝓜 R (f p) (s.map (inverseConjugationCLM p.1))) := by
    induction s using List.reverseRecOn generalizing f with
    | nil => exact (derivativeCLM 𝓜 R []).continuous.comp hf
    | append_singleton s X ih =>
        simp_rw [List.map_append, List.map_singleton, ← derivativeCoordinates_operator]
        apply ih
        exact (continuous_operator_uncurry R).comp
          (((continuous_inverseConjugationCLM_apply X).comp continuous_fst).prodMk hf)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro s
  change Continuous (fun p : Aˣ × D => derivativeCoordinates 𝓜 R (representation 𝓜 R p.1 p.2) s)
  simp_rw [derivativeCoordinates_representation_units]
  exact hR.comp (continuous_fst.prodMk (hcoord s Prod.snd continuous_snd))

end Langlands.Archimedean.DerivativeSmoothVectors
