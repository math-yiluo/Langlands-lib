import Langlands.BaseChange.TwistedLocalDescent.BlockDeterminant
import Langlands.BaseChange.WeylHaarScaling
import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.AllField.Group.GL.BlockModulus
import Langlands.LocalField.LocalFieldArithmetic
import Langlands.Group.GL.LocalFieldTopology

/-! # The weight `|D_{G/M,σ}|^{-1/2}` from the opposite nilradical

For a cyclic algebra `E/F` of nonarchimedean local fields of group `⟨σ⟩`, with `E` carrying the
`F`-module topology, the residue-normalized absolute values satisfy
`|det_F(σ − Ad(m)⁻¹ | 𝔲̄)|_F² = |D_{G/M,σ}(m)|_F · δ_P(m)`, with `δ_P` the Library's
`leviModulus`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear Module MeasureTheory
open scoped NNReal ENNReal

universe u v

section NormCompatibility

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

attribute [local instance] LocalFieldTopology.t2Space

/-- The residue-normalized absolute value of `E` is that of `F` composed with the norm. -/
theorem residueNormalizedAbsoluteValue_norm [FiniteDimensional F E] (y : E) :
    LocalField.residueNormalizedAbsoluteValue F (Algebra.norm F y) =
      LocalField.residueNormalizedAbsoluteValue E y := by
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero, map_zero, map_zero]
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let _ : MeasurableSpace F := borel F
  have _ : BorelSpace F := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  have h1 := map_mul_residueAbsolute E μ y hy
  let Lin : E ≃ₗ[F] E :=
    { toFun := fun x => y * x
      invFun := fun x => y⁻¹ * x
      map_add' := mul_add y
      map_smul' := fun c x => mul_smul_comm c y x
      left_inv := fun x => by simp [hy]
      right_inv := fun x => by simp [hy] }
  let L : E ≃L[F] E :=
    { Lin with
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have h2 := map_linearEquiv_residueAbsolute F μ L
  have hdet : L.toLinearEquiv.toLinearMap.det = Algebra.norm F y := by
    rw [Algebra.norm_apply]
    rfl
  rw [hdet] at h2
  have hmap : μ.map L = μ.map (fun x => y * x) := rfl
  rw [hmap, h1] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : E)
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hK' := congrArg (fun ν : Measure E => ν K) h2
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at hK'
  have hc : (((residueAbsoluteNNReal E y)⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (((residueAbsoluteNNReal F (Algebra.norm F y))⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.mul_left_inj hpos hfin).mp hK'
  have hc' : residueAbsoluteNNReal E y = residueAbsoluteNNReal F (Algebra.norm F y) :=
    inv_injective (ENNReal.coe_injective hc)
  have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hc'
  exact this.symm

end NormCompatibility

/-- The Library's normalized absolute value of a local field is the residue-normalized one. -/
theorem normalizedAbs_ofInstances {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (x : E) :
    (LocalFieldData.ofInstances E).normalizedAbs x = LocalField.residueNormalizedAbsoluteValue E x := by
  by_cases hx : x = 0
  · subst hx
    simp [LocalFieldData.normalizedAbs]
  rw [(LocalFieldData.ofInstances E).normalizedAbs_of_ne_zero hx,
    LocalField.residueNormalizedAbsoluteValue_of_ne_zero E hx]
  change (LocalField.residueCardinality E : ℝ) ^ (-(-WithZero.log _)) = _
  rw [neg_neg]
  rfl

section Weight

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] {n : ℕ} (B : BlockShape n)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] [IsModuleTopology F E] in
theorem det_restrictScalars_lowerAdjoint (m : B.Levi E) :
    LinearMap.det (((linearAdjoint (B.leviEmbedding E m)).restrictScalars F).restrict
      (linearAdjoint_le_lowerLie (F := F) B m)) =
      Algebra.norm F (LinearMap.det (lowerAdjoint B m)) := by
  rw [← LinearMap.det_restrictScalars]
  rfl

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
theorem det_inv_val {r : ℕ} (g : GeneralLinear r E) : ((g⁻¹ : GeneralLinear r E).val).det =
    (g.val.det)⁻¹ := by
  have h : (g⁻¹ : GeneralLinear r E).val.det * g.val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  exact eq_inv_of_mul_eq_one_left h

/-- `|det_F(Ad(m) | 𝔲̄)|_F = δ_P(m)⁻¹`. -/
theorem residueNormalizedAbsoluteValue_det_lowerAdjoint [FiniteDimensional F E] (m : B.Levi E) :
    LocalField.residueNormalizedAbsoluteValue F
        (LinearMap.det (((linearAdjoint (B.leviEmbedding E m)).restrictScalars F).restrict
          (linearAdjoint_le_lowerLie (F := F) B m))) =
      (((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ)⁻¹ := by
  classical
  let a : Fin B.length → ℝ := fun i => LocalField.residueNormalizedAbsoluteValue E (m i).val.det
  have ha : ∀ i, a i ≠ 0 := fun i => by
    simp only [a, ne_eq, map_eq_zero]
    exact (m i).isUnit.map Matrix.detMonoidHom |>.ne_zero
  rw [det_restrictScalars_lowerAdjoint, residueNormalizedAbsoluteValue_norm, det_lowerAdjoint,
    map_prod]
  have hL : (((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ) =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        a i ^ B.size j / a j ^ B.size i := by
    rw [LocalFieldData.leviModulus_apply]
    simp only [Units.coe_prod, NNReal.coe_prod, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      NNReal.coe_div, NNReal.coe_pow, LocalFieldData.determinantNorm_coe, a,
      normalizedAbs_ofInstances]
    rfl
  rw [hL, ← Finset.prod_inv_distrib]
  simp only [← Finset.prod_inv_distrib, inv_div]
  rw [Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k _
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs with h
  · simp only [map_mul, map_pow, det_inv_val, map_inv₀, a]
    rw [div_eq_mul_inv, inv_pow]
  · rfl

/-- **The weight identity.** For a cyclic algebra `E/F` of group `⟨σ⟩`,
`|det_F(σ − Ad(m)⁻¹ | 𝔲̄)|_F² = |D_{G/M,σ}(m)|_F · δ_P(m)`. -/
theorem residueNormalizedAbsoluteValue_det_twistedOperator_sq (σ : E ≃ₐ[F] E) {l : ℕ}
    (hE : IsCyclicAlgebra σ l) (m : B.Levi E) :
    haveI : FiniteDimensional F E := hE.1
    LocalField.residueNormalizedAbsoluteValue F
        (LinearMap.det ((twistedOperator B σ m).restrict (twistedOperator_le_lowerLie B σ m))) ^ 2 =
      LocalField.residueNormalizedAbsoluteValue F (twistedRelativeParabolicDiscriminant B σ m) *
        (((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ) := by
  have : FiniteDimensional F E := hE.1
  have : IsGalois F E := hE.isGalois
  have hpos : (((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (Units.ne_zero _)
  rw [abv_twistedRelativeParabolicDiscriminant B σ m _ hE.pos hE.pow_eq_one,
    residueNormalizedAbsoluteValue_det_lowerAdjoint, mul_assoc, inv_mul_cancel₀ hpos, mul_one]

end Weight

end Langlands.BaseChange.TwistedLocalDescent
