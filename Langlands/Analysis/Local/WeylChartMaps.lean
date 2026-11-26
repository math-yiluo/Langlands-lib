import Langlands.Analysis.Local.WeylChartCoordinates
import Langlands.Analysis.NonarchimedeanChangeOfVariables
import Langlands.BaseChange.OrbitChartDerivative

/-! # The product map and the conjugation chart in transverse and centralizer coordinates -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory
open scoped NNReal

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R] [FiniteDimensional F R]

/-- The transverse coordinate as a continuous linear map to the ring. -/
def transverseCLM (γ : Rˣ) : Coord F γ →L[F] R :=
  (Submodule.subtypeL _).comp (ContinuousLinearMap.fst F _ _)

/-- The centralizer coordinate as a continuous linear map to the ring. -/
def centralCLM (γ : Rˣ) : Coord F γ →L[F] R :=
  ((centralizerAlg F γ).val.toLinearMap.toContinuousLinearMap).comp
    (ContinuousLinearMap.snd F _ _)

@[simp] theorem transverseCLM_apply (γ : Rˣ) (x : Coord F γ) :
    transverseCLM γ x = (x.1 : R) := rfl

@[simp] theorem centralCLM_apply (γ : Rˣ) (x : Coord F γ) :
    centralCLM γ x = (x.2 : R) := rfl

/-- The product map `(y, s) ↦ (1 + y)(1 + s) - 1`. -/
def productMap (γ : Rˣ) (x : Coord F γ) : R :=
  (1 + (x.1 : R)) * (1 + (x.2 : R)) - 1

theorem productMap_zero (γ : Rˣ) : productMap γ (0 : Coord F γ) = 0 := by
  simp [productMap]

theorem hasStrictFDerivAt_productMap {γ : Rˣ} (hγ : IsRegularPosition F γ) :
    HasStrictFDerivAt (productMap γ) ((coordCLE hγ : Coord F γ ≃L[F] R) : Coord F γ →L[F] R)
      0 := by
  have hQ := ((transverseCLM γ).hasStrictFDerivAt (x := (0 : Coord F γ))).const_add (1 : R)
  have hP := ((centralCLM γ).hasStrictFDerivAt (x := (0 : Coord F γ))).const_add (1 : R)
  have h := (hQ.mul' hP).sub_const (1 : R)
  have hD : ((1 + transverseCLM (F := F) γ 0) • centralCLM γ +
      MulOpposite.op (1 + centralCLM (F := F) γ 0) • transverseCLM γ : Coord F γ →L[F] R) =
      ((coordCLE hγ : Coord F γ ≃L[F] R) : Coord F γ →L[F] R) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [coordCLE_apply hγ, add_comm]
  rw [hD] at h
  exact h

/-- The conjugation chart `(y, s) ↦ (1 + y)(1 + s) γ (1 + y)⁻¹ γ⁻¹`, with the ring inverse. -/
def conjChart (γ : Rˣ) : Coord F γ → R :=
  Langlands.BaseChange.normalizedOrbitChart γ (ContinuousLinearMap.id F R) (centralCLM γ)
    (transverseCLM γ)

theorem conjChart_apply (γ : Rˣ) (x : Coord F γ) :
    conjChart γ x = (1 + (x.1 : R)) * (1 + (x.2 : R)) * (γ : R) *
      Ring.inverse (1 + (x.1 : R)) * ((γ⁻¹ : Rˣ) : R) := rfl

theorem conjChart_zero (γ : Rˣ) : conjChart γ (0 : Coord F γ) = 1 :=
  Langlands.BaseChange.normalizedOrbitChart_zero γ _ rfl _ _

theorem mem_ker_defect_iff {γ : Rˣ} (x : R) :
    x ∈ LinearMap.ker (defect F γ) ↔ x ∈ (centralizerAlg F γ).toSubmodule := by
  rw [LinearMap.mem_ker, defect_apply, sub_eq_zero, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_centralizer_iff]
  constructor
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc (γ : R) * x = (γ : R) * x * ((γ⁻¹ : Rˣ) : R) * (γ : R) := by
          rw [mul_assoc _ ((γ⁻¹ : Rˣ) : R), Units.inv_mul, mul_one]
      _ = x * (γ : R) := by rw [h]
  · intro h
    have h1 := h (γ : R) (Set.mem_singleton _)
    rw [h1, mul_assoc, Units.mul_inv, mul_one]

/-- The adjoint defect restricted to transverse directions. -/
def transverseDefect (γ : Rˣ) :
    LinearMap.range (defect F γ) →ₗ[F] LinearMap.range (defect F γ) :=
  (defect F γ).restrict fun y _ => LinearMap.mem_range_self _ y

theorem transverseDefect_bijective {γ : Rˣ} (hγ : IsRegularPosition F γ) :
    Function.Bijective (transverseDefect (F := F) γ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hd : defect F γ y = 0 := congrArg Subtype.val hy
    have hker : (y : R) ∈ (centralizerAlg F γ).toSubmodule :=
      (mem_ker_defect_iff (y : R)).1 hd
    have := hγ.disjoint.le_bot ⟨y.property, hker⟩
    exact Subtype.ext ((Submodule.mem_bot F).1 this)
  · rintro ⟨z, w, rfl⟩
    have hw : w ∈ LinearMap.range (defect F γ) ⊔ (centralizerAlg F γ).toSubmodule := by
      rw [hγ.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hw
    refine ⟨⟨w₁, hw₁⟩, Subtype.ext ?_⟩
    have h₂ : defect F γ w₂ = 0 := (mem_ker_defect_iff w₂).2 hw₂
    change defect F γ w₁ = defect F γ (w₁ + w₂)
    rw [map_add, h₂, add_zero]

/-- The linearized chart in coordinates: `(y, s) ↦ (-(γ y γ⁻¹ - y), s)`. -/
def chartCoordEquiv {γ : Rˣ} (hγ : IsRegularPosition F γ) : Coord F γ ≃ₗ[F] Coord F γ :=
  LinearEquiv.ofBijective ((-transverseDefect (F := F) γ).prodMap LinearMap.id)
    (by
      have hb := transverseDefect_bijective hγ
      refine ⟨?_, ?_⟩
      · rintro ⟨a, b⟩ ⟨c, d⟩ h
        simp only [LinearMap.prodMap_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq,
          Prod.mk.injEq, neg_inj] at h
        exact Prod.ext (hb.1 h.1) h.2
      · rintro ⟨a, b⟩
        obtain ⟨c, hc⟩ := hb.2 (-a)
        exact ⟨(c, b), by simp [hc]⟩)

/-- The derivative of the conjugation chart at zero. -/
def chartDerivative {γ : Rˣ} (hγ : IsRegularPosition F γ) : Coord F γ ≃L[F] R :=
  ((chartCoordEquiv hγ).toContinuousLinearEquiv).trans (coordCLE hγ)

theorem chartDerivative_apply {γ : Rˣ} (hγ : IsRegularPosition F γ) (x : Coord F γ) :
    chartDerivative hγ x = (x.1 : R) + (x.2 : R) - (γ : R) * (x.1 : R) * ((γ⁻¹ : Rˣ) : R) := by
  change coordCLE hγ (chartCoordEquiv hγ x) = _
  rw [coordCLE_apply hγ]
  change (((-transverseDefect (F := F) γ) x.1 : LinearMap.range (defect F γ)) : R) + (x.2 : R) = _
  simp only [LinearMap.neg_apply, Submodule.coe_neg]
  change -(defect F γ (x.1 : R)) + (x.2 : R) = _
  rw [defect_apply]
  abel

theorem hasStrictFDerivAt_conjChart [CompleteSpace R] {γ : Rˣ} (hγ : IsRegularPosition F γ) :
    HasStrictFDerivAt (conjChart γ)
      ((chartDerivative hγ : Coord F γ ≃L[F] R) : Coord F γ →L[F] R) 0 := by
  have h := Langlands.BaseChange.orbitChartDerivative γ (ContinuousLinearMap.id F R) rfl
    (centralCLM γ) (transverseCLM (F := F) γ)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearEquiv.coe_coe, chartDerivative_apply]
  simp [ContinuousLinearMap.mulLeftRight_apply, add_comm, mul_assoc]

end Langlands.Analysis.WeylChart
