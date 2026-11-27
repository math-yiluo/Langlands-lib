import Langlands.BaseChange.TwistedLocalDescent.DiscriminantWeight
import Langlands.BaseChange.TwistedLocalDescent.Iwahori
import Langlands.BaseChange.TwistedLocalDescent.RescaleBound
import Langlands.BaseChange.RelativeParabolicDiscriminantRegular

/-! # The linear part of the twisted chart over a cyclic extension

For a cyclic algebra `E/F` of nonarchimedean local fields of group `⟨σ⟩`, with `E` carrying the
`F`-module topology, and `m ∈ M(E)`, the linear part of the twisted chart at `m` is the `F`-linear
map `A(X) = X_𝔭 + T(X_𝔲̄)`, `T = σ − Ad(m)⁻¹`. Its determinant over `F` is that of `T` on `𝔲̄`. When
the twisted relative discriminant at `m` is nonzero, `A` is a continuous `F`-linear automorphism of
`M_n(E)`; it scales additive Haar measure by `|det_F A|_F⁻¹`, its inverse is bounded for the local
norm, and `δ_P(m)^{1/2} |det_F A|_F⁻¹ = |D_{G/M,σ}(m)|_F^{-1/2}`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear MeasureTheory Measure Metric Set
open scoped NNReal ENNReal

universe u v

section Linear

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {n : ℕ} (B : BlockShape n)
  (σ : E ≃ₐ[F] E)

/-- The strictly block lower part, as an `F`-linear map. -/
def lowerPartLinear : Matrix (Fin n) (Fin n) E →ₗ[F] Matrix (Fin n) (Fin n) E where
  toFun X := Matrix.of fun a b => if B.coordinateBlock b < B.coordinateBlock a then X a b else 0
  map_add' X Y := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c X := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem lowerPartLinear_apply_mem (X : Matrix (Fin n) (Fin n) E) :
    lowerPartLinear (F := F) B X ∈ lowerLie (E := E) B := by
  intro a b h
  simp [lowerPartLinear, not_lt.mpr h]

theorem lowerPartLinear_of_mem {Z : Matrix (Fin n) (Fin n) E} (hZ : Z ∈ lowerLie (E := E) B) :
    lowerPartLinear (F := F) B Z = Z := by
  ext a b
  simp only [lowerPartLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact (hZ a b (not_lt.mp h)).symm

/-- `X ↦ X_𝔭 + T(X_𝔲̄)` with `T = σ − Ad(m)⁻¹`, as an `F`-linear map. -/
def chartLinear (m : B.Levi E) : Matrix (Fin n) (Fin n) E →ₗ[F] Matrix (Fin n) (Fin n) E :=
  LinearMap.id - lowerPartLinear B + twistedOperator B σ m ∘ₗ lowerPartLinear B

theorem chartLinear_apply (m : B.Levi E) (X : Matrix (Fin n) (Fin n) E) :
    chartLinear B σ m X = (X - lowerPartLinear (F := F) B X) +
      twistedOperator B σ m (lowerPartLinear (F := F) B X) := rfl

theorem chartLinear_le_lowerLie (m : B.Levi E) :
    (lowerLie (E := E) B).restrictScalars F ≤
      ((lowerLie (E := E) B).restrictScalars F).comap (chartLinear B σ m) := by
  intro Z hZ
  change chartLinear B σ m Z ∈ lowerLie (E := E) B
  rw [chartLinear_apply, lowerPartLinear_of_mem B hZ, sub_self, zero_add]
  exact twistedOperator_le_lowerLie B σ m hZ

variable [FiniteDimensional F E]

/-- **`det_F A = det_F(T|𝔲̄)`.** -/
theorem det_chartLinear (m : B.Levi E) :
    LinearMap.det (chartLinear B σ m) =
      LinearMap.det ((twistedOperator B σ m).restrict (twistedOperator_le_lowerLie B σ m)) := by
  rw [LinearMap.det_eq_det_mul_det ((lowerLie (E := E) B).restrictScalars F) _
    (chartLinear_le_lowerLie B σ m)]
  have hres : (chartLinear B σ m).restrict (chartLinear_le_lowerLie B σ m) =
      (twistedOperator B σ m).restrict (p := (lowerLie (E := E) B).restrictScalars F)
        (q := (lowerLie (E := E) B).restrictScalars F) (twistedOperator_le_lowerLie B σ m) := by
    apply LinearMap.ext
    intro Z
    apply Subtype.ext
    change chartLinear B σ m Z = twistedOperator B σ m Z
    rw [chartLinear_apply, lowerPartLinear_of_mem B Z.property, sub_self, zero_add]
  have hQ : ((lowerLie (E := E) B).restrictScalars F).mapQ
      ((lowerLie (E := E) B).restrictScalars F) (chartLinear B σ m)
        (chartLinear_le_lowerLie B σ m) = LinearMap.id := by
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on _ q fun X => ?_
    rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]
    change chartLinear B σ m X - X ∈ lowerLie (E := E) B
    rw [chartLinear_apply]
    have : X - lowerPartLinear (F := F) B X +
        twistedOperator B σ m (lowerPartLinear (F := F) B X) - X =
        twistedOperator B σ m (lowerPartLinear (F := F) B X) - lowerPartLinear (F := F) B X := by
      abel
    rw [this]
    exact sub_mem (twistedOperator_le_lowerLie B σ m (lowerPartLinear_apply_mem B X))
      (lowerPartLinear_apply_mem B X)
  rw [hres, hQ, LinearMap.det_id, mul_one]

end Linear

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] {n : ℕ} (B : BlockShape n) (σ : E ≃ₐ[F] E)

/-- At a Levi element with nonzero twisted relative discriminant, `det_F A ≠ 0`. -/
theorem det_chartLinear_ne_zero {l : ℕ} (hE : IsCyclicAlgebra σ l) (m : B.Levi E)
    (hD : (haveI : FiniteDimensional F E := hE.1
      twistedRelativeParabolicDiscriminant B σ m) ≠ 0) :
    haveI : FiniteDimensional F E := hE.1
    LinearMap.det (chartLinear B σ m) ≠ 0 := by
  have : FiniteDimensional F E := hE.1
  rw [det_chartLinear]
  intro h0
  have hsq := residueNormalizedAbsoluteValue_det_twistedOperator_sq B σ hE m
  have hpos : (((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (Units.ne_zero _)
  have hDabs : LocalField.residueNormalizedAbsoluteValue F
      (twistedRelativeParabolicDiscriminant B σ m) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff _).mpr hD
  rw [h0, map_zero, zero_pow two_ne_zero] at hsq
  exact mul_ne_zero hDabs hpos hsq.symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [IsNonarchimedeanLocalField E] in
theorem matrix_isModuleTopology :
    IsModuleTopology F (Matrix (Fin n) (Fin n) E) :=
  inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))

attribute [local instance] matrix_isModuleTopology

/-- The linear part of the twisted chart as a continuous `F`-linear automorphism. -/
def chartLinearEquiv [FiniteDimensional F E] (m : B.Levi E)
    (h : LinearMap.det (chartLinear B σ m) ≠ 0) :
    Matrix (Fin n) (Fin n) E ≃L[F] Matrix (Fin n) (Fin n) E where
  toLinearEquiv := LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr h)
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr h)).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr h)).symm.toLinearMap

@[simp]
theorem chartLinearEquiv_apply [FiniteDimensional F E] (m : B.Levi E)
    (h : LinearMap.det (chartLinear B σ m) ≠ 0) (X : Matrix (Fin n) (Fin n) E) :
    chartLinearEquiv B σ m h X = chartLinear B σ m X :=
  LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr h) X

/-- **Haar scaling by the chart's linear part.** -/
theorem map_chartLinearEquiv [FiniteDimensional F E] (m : B.Levi E)
    (h : LinearMap.det (chartLinear B σ m) ≠ 0)
    [MeasurableSpace (Matrix (Fin n) (Fin n) E)] [BorelSpace (Matrix (Fin n) (Fin n) E)]
    (ν : Measure (Matrix (Fin n) (Fin n) E)) [ν.IsAddHaarMeasure] :
    ν.map (chartLinearEquiv B σ m h) =
      ((residueAbsoluteNNReal F (LinearMap.det (chartLinear B σ m)))⁻¹ : ℝ≥0) • ν := by
  let _ : MeasurableSpace F := borel F
  have _ : BorelSpace F := ⟨rfl⟩
  have := map_linearEquiv_residueAbsolute F (X := Matrix (Fin n) (Fin n) E) ν
    (chartLinearEquiv B σ m h)
  have hL : (chartLinearEquiv B σ m h).toLinearEquiv.toLinearMap = chartLinear B σ m :=
    LinearMap.coe_equivOfIsUnitDet (isUnit_iff_ne_zero.mpr h)
  rw [this, hL]

/-- **The weight identity.** `δ_P(m)^{1/2} |det_F A|_F⁻¹ = |D_{G/M,σ}(m)|_F^{-1/2}`. -/
theorem sqrt_leviModulus_mul_inv_det_chartLinear {l : ℕ} (hE : IsCyclicAlgebra σ l)
    (m : B.Levi E) :
    haveI : FiniteDimensional F E := hE.1
    (NNReal.sqrt ((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ) *
        (((residueAbsoluteNNReal F (LinearMap.det (chartLinear B σ m)))⁻¹ : ℝ≥0) : ℝ) =
      (Real.sqrt (LocalField.residueNormalizedAbsoluteValue F
        (twistedRelativeParabolicDiscriminant B σ m)))⁻¹ := by
  have : FiniteDimensional F E := hE.1
  have hsq := residueNormalizedAbsoluteValue_det_twistedOperator_sq B σ hE m
  rw [← det_chartLinear] at hsq
  set a := LocalField.residueNormalizedAbsoluteValue F (LinearMap.det (chartLinear B σ m))
  set D := LocalField.residueNormalizedAbsoluteValue F (twistedRelativeParabolicDiscriminant B σ m)
  set μ := (((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ)
  have ha : 0 ≤ a := AbsoluteValue.nonneg _ _
  have hD : 0 ≤ D := AbsoluteValue.nonneg _ _
  have hμ : 0 < μ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hsμ : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.mpr hμ).ne'
  have ha_eq : a = Real.sqrt D * Real.sqrt μ := by
    rw [← Real.sqrt_mul hD, ← hsq, Real.sqrt_sq ha]
  have h1 : (NNReal.sqrt ((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ) =
      Real.sqrt μ := Real.coe_sqrt
  have h2 : (((residueAbsoluteNNReal F (LinearMap.det (chartLinear B σ m)))⁻¹ : ℝ≥0) : ℝ) =
      a⁻¹ := by
    rw [NNReal.coe_inv]
    rfl
  rw [h1, h2, ha_eq, mul_inv, mul_left_comm, mul_inv_cancel₀ hsμ, mul_one]

section Normed

noncomputable local instance normedE : NontriviallyNormedField E := LocalGalois.localNormedField E

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The `F`-linear map `chartLinear` is the linear part of the twisted chart. -/
theorem chartLinear_eq_twistedChartLinear (m : B.Levi E) (X : Matrix (Fin n) (Fin n) E) :
    chartLinear B σ m X = twistedChartLinear B (σ : E →+* E) (B.leviEmbedding E m).val
      ((B.leviEmbedding E m)⁻¹).val X := by
  rw [chartLinear_apply]
  change (X - lowerPart B X) + (matrixSigma σ (lowerPart B X) -
      linearAdjoint (B.leviEmbedding E m⁻¹) (lowerPart B X)) = _
  simp only [twistedChartLinear, upperPart, linearAdjoint, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_inv, inv_inv]
  have hσ : matrixSigma σ (lowerPart B X) = (lowerPart B X).map (σ : E →+* E) := rfl
  rw [hσ, mul_assoc]
  abel

/-- The inverse of the chart's linear part is bounded for the local sup norm. -/
theorem exists_norm_symm_chartLinearEquiv_le [FiniteDimensional F E] (m : B.Levi E)
    (h : LinearMap.det (chartLinear B σ m) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ Y : Matrix (Fin n) (Fin n) E,
      ‖(chartLinearEquiv B σ m h).symm Y‖ ≤ C * ‖Y‖ := by
  obtain ⟨a, ha⟩ := exists_one_lt_norm_algebraMap (F := F) (E := E)
  refine exists_norm_le_of_continuous_of_map_smul (𝕜 := E)
    (chartLinearEquiv B σ m h).symm.toLinearEquiv.toAddEquiv.toAddMonoidHom
    (chartLinearEquiv B σ m h).symm.continuous ha fun Y => ?_
  change (chartLinearEquiv B σ m h).symm (algebraMap F E a • Y) =
    algebraMap F E a • (chartLinearEquiv B σ m h).symm Y
  rw [algebraMap_smul, algebraMap_smul, map_smul]

end Normed

end LocalField

end Langlands.BaseChange.TwistedLocalDescent
