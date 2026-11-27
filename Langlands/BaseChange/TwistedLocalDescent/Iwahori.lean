import Langlands.BaseChange.TwistedLocalDescent.ParabolicHaar
import Langlands.BaseChange.TwistedLocalDescent.ChartEstimate
import Langlands.BaseChange.TwistedLocalDescent.OneBall

/-! # The Iwahori factorization of Haar measure on a congruence ball

Square matrices split as the sum `M_n = 𝔭 ⊕ 𝔲̄` of block upper triangular matrices and strictly
block lower matrices. Over an ultrametric proper nontrivially normed field, additive Haar
measures on the two summands give an additive Haar measure on `M_n`, and for `0 < r < 1` the map
`(X, Z) ↦ X (1 + Z)` sends the product of these measures, restricted to the balls of radius `r`
about `1 ∈ 𝔭` and `0 ∈ 𝔲̄`, to the assembled measure on `M_n` restricted to the ball of radius `r`
about `1`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe v

section Decomposition

attribute [local instance] Matrix.normedAddCommGroup matrix_isUltrametricDist

variable {𝕂 : Type v} [NormedField 𝕂] {n : ℕ} (B : BlockShape n)

theorem upperPart_mem (X : Matrix (Fin n) (Fin n) 𝕂) :
    upperPart B X ∈ parabolicSubalgebra (R := 𝕂) B := by
  rw [Matrix.mem_blockTriangularSubalgebra]
  intro a c h
  simp [upperPart, lowerPart, h]

theorem lowerPart_mem (X : Matrix (Fin n) (Fin n) 𝕂) : lowerPart B X ∈ lowerLie (E := 𝕂) B :=
  lowerPart_isLower B X

theorem lowerPart_eq_zero_of_mem {W : Matrix (Fin n) (Fin n) 𝕂}
    (hW : W ∈ parabolicSubalgebra (R := 𝕂) B) : lowerPart B W = 0 := by
  ext a c
  simp only [lowerPart, Matrix.of_apply, Matrix.zero_apply]
  split_ifs with h
  · exact (Matrix.mem_blockTriangularSubalgebra.mp hW) h
  · rfl

theorem lowerPart_eq_self_of_mem {Z : Matrix (Fin n) (Fin n) 𝕂}
    (hZ : Z ∈ lowerLie (E := 𝕂) B) : lowerPart B Z = Z := by
  ext a c
  simp only [lowerPart, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact (hZ a c (not_lt.mp h)).symm

theorem lowerPart_add (X Y : Matrix (Fin n) (Fin n) 𝕂) :
    lowerPart B (X + Y) = lowerPart B X + lowerPart B Y := by
  ext a c
  simp only [lowerPart, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem lowerPart_add_of_mem {W Z : Matrix (Fin n) (Fin n) 𝕂}
    (hW : W ∈ parabolicSubalgebra (R := 𝕂) B) (hZ : Z ∈ lowerLie (E := 𝕂) B) :
    lowerPart B (W + Z) = Z := by
  rw [lowerPart_add, lowerPart_eq_zero_of_mem B hW, lowerPart_eq_self_of_mem B hZ, zero_add]

theorem upperPart_add_of_mem {W Z : Matrix (Fin n) (Fin n) 𝕂}
    (hW : W ∈ parabolicSubalgebra (R := 𝕂) B) (hZ : Z ∈ lowerLie (E := 𝕂) B) :
    upperPart B (W + Z) = W := by
  rw [upperPart, lowerPart_add_of_mem B hW hZ, add_sub_cancel_right]

theorem upperPart_add_lowerPart (X : Matrix (Fin n) (Fin n) 𝕂) :
    upperPart B X + lowerPart B X = X :=
  sub_add_cancel X _

/-- The additive decomposition `M_n = 𝔭 ⊕ 𝔲̄`. -/
def blockSumAddEquiv :
    (parabolicSubalgebra (R := 𝕂) B) × (lowerLie (E := 𝕂) B) ≃+ Matrix (Fin n) (Fin n) 𝕂 where
  toFun q := (q.1 : Matrix (Fin n) (Fin n) 𝕂) + q.2
  invFun X := (⟨upperPart B X, upperPart_mem B X⟩, ⟨lowerPart B X, lowerPart_mem B X⟩)
  left_inv q := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact upperPart_add_of_mem B q.1.2 q.2.2
    · exact lowerPart_add_of_mem B q.1.2 q.2.2
  right_inv X := upperPart_add_lowerPart B X
  map_add' q q' := by
    simp only [Prod.fst_add, Prod.snd_add, Subalgebra.coe_add, Submodule.coe_add]
    abel

@[simp]
theorem blockSumAddEquiv_apply
    (q : (parabolicSubalgebra (R := 𝕂) B) × (lowerLie (E := 𝕂) B)) :
    blockSumAddEquiv B q = (q.1 : Matrix (Fin n) (Fin n) 𝕂) + q.2 := rfl

theorem continuous_lowerPart : Continuous (lowerPart (𝕂 := 𝕂) B) := by
  refine continuous_pi fun a => continuous_pi fun c => ?_
  simp only [lowerPart, Matrix.of_apply]
  split_ifs
  · exact continuous_id.matrix_elem a c
  · exact continuous_const

theorem continuous_upperPart : Continuous (upperPart (𝕂 := 𝕂) B) :=
  continuous_id.sub (continuous_lowerPart B)

/-- The decomposition `M_n = 𝔭 ⊕ 𝔲̄` as a homeomorphism. -/
def blockSumHomeomorph :
    (parabolicSubalgebra (R := 𝕂) B) × (lowerLie (E := 𝕂) B) ≃ₜ Matrix (Fin n) (Fin n) 𝕂 where
  toEquiv := (blockSumAddEquiv B).toEquiv
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  continuous_invFun :=
    ((continuous_upperPart B).subtype_mk _).prodMk ((continuous_lowerPart B).subtype_mk _)

theorem norm_add_of_mem [IsUltrametricDist 𝕂] {W Z : Matrix (Fin n) (Fin n) 𝕂}
    (hW : W ∈ parabolicSubalgebra (R := 𝕂) B) (hZ : Z ∈ lowerLie (E := 𝕂) B) :
    ‖W + Z‖ = max ‖W‖ ‖Z‖ := by
  refine le_antisymm (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
  · calc ‖W‖ = ‖upperPart B (W + Z)‖ := by rw [upperPart_add_of_mem B hW hZ]
      _ ≤ ‖W + Z‖ := norm_upperPart_le B _
  · calc ‖Z‖ = ‖lowerPart B (W + Z)‖ := by rw [lowerPart_add_of_mem B hW hZ]
      _ ≤ ‖W + Z‖ := norm_lowerPart_le B _

/-- The unipotent element `1 + Z` for a strictly block lower `Z`. -/
def lowerUnit (Z : lowerLie (E := 𝕂) B) : GeneralLinear n 𝕂 where
  val := 1 + (Z : Matrix (Fin n) (Fin n) 𝕂)
  inv := lowerInverse B (Z : Matrix (Fin n) (Fin n) 𝕂)
  val_inv := one_add_mul_lowerInverse B Z.property
  inv_val := lowerInverse_mul_one_add B Z.property

@[simp]
theorem lowerUnit_val (Z : lowerLie (E := 𝕂) B) :
    (lowerUnit B Z).val = 1 + (Z : Matrix (Fin n) (Fin n) 𝕂) := rfl

theorem continuous_lowerUnit : Continuous (lowerUnit (𝕂 := 𝕂) B) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_const.add continuous_subtype_val, ?_⟩
  change Continuous fun Z : lowerLie (E := 𝕂) B =>
    ∑ t ∈ Finset.range B.length, (-(Z : Matrix (Fin n) (Fin n) 𝕂)) ^ t
  exact continuous_finsetSum _ fun t _ => (continuous_subtype_val.neg).pow t

theorem isClosed_lowerLie :
    IsClosed (lowerLie (E := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)) := by
  have : (lowerLie (E := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)) =
      ⋂ a, ⋂ c, ⋂ (_ : B.coordinateBlock a ≤ B.coordinateBlock c),
        {M : Matrix (Fin n) (Fin n) 𝕂 | M a c = 0} := by
    ext M
    simp only [SetLike.mem_coe, mem_iInter, mem_ofPred_eq]
    rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun c => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem a c) continuous_const

end Decomposition

section Coordinates

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace matrix_locallyCompactSpace
  parabolicSubalgebra_locallyCompact parabolicSubalgebra_isTopologicalRing

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} (B : BlockShape n)

omit [IsUltrametricDist 𝕂] in
theorem lowerLie_locallyCompact : LocallyCompactSpace (lowerLie (E := 𝕂) B) :=
  (isClosed_lowerLie B).isClosedEmbedding_subtypeVal.locallyCompactSpace

omit [IsUltrametricDist 𝕂] in
theorem matrix_secondCountable : SecondCountableTopology (Matrix (Fin n) (Fin n) 𝕂) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → 𝕂))

attribute [local instance] lowerLie_locallyCompact matrix_secondCountable

omit [IsUltrametricDist 𝕂] in
theorem lowerLie_secondCountable : SecondCountableTopology (lowerLie (E := 𝕂) B) :=
  inferInstanceAs (SecondCountableTopology (lowerLie (E := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)))

omit [IsUltrametricDist 𝕂] in
theorem parabolicSubalgebra_secondCountable :
    SecondCountableTopology (parabolicSubalgebra (R := 𝕂) B) :=
  inferInstanceAs (SecondCountableTopology
    (parabolicSubalgebra (R := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)))

attribute [local instance] lowerLie_secondCountable parabolicSubalgebra_secondCountable

omit [ProperSpace 𝕂] in
/-- Lipschitz estimate for the perturbation `X ↦ X_𝔭 X_𝔲̄` on the ball of radius `r`. -/
theorem lipschitzOnWith_upperPart_mul_lowerPart {r : ℝ} (hr0 : 0 ≤ r) :
    LipschitzOnWith ⟨r, hr0⟩ (fun X : Matrix (Fin n) (Fin n) 𝕂 => upperPart B X * lowerPart B X)
      (closedBall 0 r) := by
  refine LipschitzOnWith.of_dist_le_mul fun X hX Y hY => ?_
  rw [mem_closedBall_zero_iff] at hX hY
  rw [dist_eq_norm, dist_eq_norm]
  change ‖upperPart B X * lowerPart B X - upperPart B Y * lowerPart B Y‖ ≤ r * ‖X - Y‖
  refine (norm_mul_sub_mul_le _ _ _ _).trans (max_le ?_ ?_)
  · rw [upperPart_sub, mul_comm r]
    exact mul_le_mul (norm_upperPart_le B _) ((norm_lowerPart_le B X).trans hX)
      (norm_nonneg _) (norm_nonneg _)
  · rw [lowerPart_sub]
    exact mul_le_mul ((norm_upperPart_le B Y).trans hY) (norm_lowerPart_le B _)
      (norm_nonneg _) hr0

theorem lipschitzOnWith_congr' {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f g : α → β} {s : Set α} (hf : LipschitzOnWith K f s)
    (h : ∀ x ∈ s, f x = g x) : LipschitzOnWith K g s := by
  intro x hx y hy
  rw [← h x hx, ← h y hy]
  exact hf hx hy

variable [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)]

/-- Haar measure on the ball of radius `r < 1` is invariant under `X ↦ X + X_𝔭 X_𝔲̄`. -/
theorem map_restrict_closedBall_perturbation (ν : Measure (Matrix (Fin n) (Fin n) 𝕂))
    [ν.IsAddHaarMeasure] {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (ν.restrict (closedBall 0 r)).map (fun X => X + upperPart B X * lowerPart B X) =
      ν.restrict (closedBall 0 r) := by
  let k : ℝ≥0 := ⟨r, hr0.le⟩
  have hk : k < 1 := NNReal.coe_lt_coe.mp hr1
  have h := map_restrict_closedBall_of_perturbation' (by rfl) ν (Homeomorph.refl _) 1
    (by
      change Measure.map id ν = 1 • ν
      rw [Measure.map_id, one_smul]) (fun X => X + upperPart B X * lowerPart B X)
    (((continuous_upperPart B).mul (continuous_lowerPart B)).congr fun X =>
      (add_sub_cancel_left X _).symm)
    hr0.le hk
    (lipschitzOnWith_congr' (lipschitzOnWith_upperPart_mul_lowerPart B hr0.le) fun X _ =>
      (add_sub_cancel_left X _).symm)
    (by simp [lowerPart_eq_zero_of_mem B (zero_mem _)]) rfl
  rw [one_smul] at h
  convert h using 2
  exact (image_id _).symm

/-- The additive Haar measure on `M_n` assembled from additive Haar measures on `𝔭` and `𝔲̄`. -/
def blockSumMeasure (νS : Measure (parabolicSubalgebra (R := 𝕂) B))
    (νL : Measure (lowerLie (E := 𝕂) B)) : Measure (Matrix (Fin n) (Fin n) 𝕂) :=
  (νS.prod νL).map (blockSumAddEquiv B)

instance blockSumMeasure_isAddHaarMeasure (νS : Measure (parabolicSubalgebra (R := 𝕂) B))
    [νS.IsAddHaarMeasure] (νL : Measure (lowerLie (E := 𝕂) B)) [νL.IsAddHaarMeasure] :
    (blockSumMeasure B νS νL).IsAddHaarMeasure := by
  unfold blockSumMeasure
  exact AddEquiv.isAddHaarMeasure_map (νS.prod νL) (blockSumAddEquiv B)
    (blockSumHomeomorph (𝕂 := 𝕂) B).continuous (blockSumHomeomorph (𝕂 := 𝕂) B).symm.continuous

/-- The ball of radius `r` about `0` corresponds to the product of the balls in `𝔭` and `𝔲̄`. -/
theorem blockSumMeasure_restrict_closedBall_zero (νS : Measure (parabolicSubalgebra (R := 𝕂) B))
    [SFinite νS] (νL : Measure (lowerLie (E := 𝕂) B)) [SFinite νL] (r : ℝ) :
    (blockSumMeasure B νS νL).restrict (closedBall 0 r) =
      ((νS.restrict (Subtype.val ⁻¹' closedBall 0 r)).prod
        (νL.restrict (Subtype.val ⁻¹' closedBall 0 r))).map (blockSumAddEquiv B) := by
  have hemb : MeasurableEmbedding (blockSumAddEquiv B) :=
    (blockSumHomeomorph (𝕂 := 𝕂) B).measurableEmbedding
  have hpre : (blockSumAddEquiv B) ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r =
      (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r) ×ˢ
        (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r) := by
    ext q
    simp only [mem_preimage, blockSumAddEquiv_apply, mem_closedBall_zero_iff, mem_prod,
      norm_add_of_mem B q.1.2 q.2.2, max_le_iff]
  rw [blockSumMeasure, hemb.restrict_map, hpre, Measure.prod_restrict]

/-- Translation by `1` inside `𝔭`. -/
theorem restrict_closedBall_one_eq_map (νS : Measure (parabolicSubalgebra (R := 𝕂) B))
    [νS.IsAddHaarMeasure] (r : ℝ) :
    νS.restrict (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r) =
      (νS.restrict (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)).map
        (fun W => (1 : parabolicSubalgebra (R := 𝕂) B) + W) := by
  have hemb : MeasurableEmbedding
      (fun W : parabolicSubalgebra (R := 𝕂) B => (1 : parabolicSubalgebra (R := 𝕂) B) + W) :=
    (Homeomorph.addLeft (1 : parabolicSubalgebra (R := 𝕂) B)).measurableEmbedding
  conv_lhs => rw [← map_add_left_eq_self νS (1 : parabolicSubalgebra (R := 𝕂) B),
    hemb.restrict_map]
  congr 2
  ext W
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, Subalgebra.coe_add,
    OneMemClass.coe_one, add_sub_cancel_left, sub_zero]

omit [ProperSpace 𝕂] in
/-- Translation by `1` in `M_n`. -/
theorem map_one_add_restrict_closedBall_zero (ν : Measure (Matrix (Fin n) (Fin n) 𝕂))
    [ν.IsAddHaarMeasure] (r : ℝ) :
    (ν.restrict (closedBall 0 r)).map (fun X => 1 + X) = ν.restrict (closedBall 1 r) := by
  have hemb : MeasurableEmbedding (fun X : Matrix (Fin n) (Fin n) 𝕂 => 1 + X) :=
    (Homeomorph.addLeft (1 : Matrix (Fin n) (Fin n) 𝕂)).measurableEmbedding
  conv_rhs => rw [← map_add_left_eq_self ν 1, hemb.restrict_map]
  congr 2
  ext X
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero]

/-- **Iwahori factorization in additive coordinates.** -/
theorem map_mul_one_add_restrict (νS : Measure (parabolicSubalgebra (R := 𝕂) B))
    [νS.IsAddHaarMeasure] (νL : Measure (lowerLie (E := 𝕂) B)) [νL.IsAddHaarMeasure]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((νS.restrict (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r)).prod
        (νL.restrict (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r))).map
      (fun q => (q.1 : Matrix (Fin n) (Fin n) 𝕂) * (1 + q.2)) =
      (blockSumMeasure B νS νL).restrict (closedBall 1 r) := by
  set ν := blockSumMeasure B νS νL
  let one : parabolicSubalgebra (R := 𝕂) B := 1
  have htrS : νS.restrict (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r) =
      (νS.restrict (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)).map
        (fun W => one + W) := by
    have hemb : MeasurableEmbedding (fun W : parabolicSubalgebra (R := 𝕂) B => one + W) :=
      (Homeomorph.addLeft one).measurableEmbedding
    conv_lhs => rw [← map_add_left_eq_self νS one, hemb.restrict_map]
    congr 2
    ext W
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, Subalgebra.coe_add, one,
      OneMemClass.coe_one, add_sub_cancel_left, sub_zero]
  let χ₀ : Matrix (Fin n) (Fin n) 𝕂 → Matrix (Fin n) (Fin n) 𝕂 :=
    fun X => X + upperPart B X * lowerPart B X
  have hχ₀ := map_restrict_closedBall_perturbation B ν hr0 hr1
  have htr : (ν.restrict (closedBall 0 r)).map (fun X => 1 + X) =
      ν.restrict (closedBall 1 r) := by
    have hemb : MeasurableEmbedding (fun X : Matrix (Fin n) (Fin n) 𝕂 => 1 + X) :=
      (Homeomorph.addLeft (1 : Matrix (Fin n) (Fin n) 𝕂)).measurableEmbedding
    conv_rhs => rw [← map_add_left_eq_self ν 1, hemb.restrict_map]
    congr 2
    ext X
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hfun : (fun q : (parabolicSubalgebra (R := 𝕂) B) × (lowerLie (E := 𝕂) B) =>
        (q.1 : Matrix (Fin n) (Fin n) 𝕂) * (1 + q.2)) ∘ Prod.map (fun W => one + W) id =
      (fun X => 1 + X) ∘ χ₀ ∘ blockSumAddEquiv B := by
    funext q
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, Subalgebra.coe_add,
      one, OneMemClass.coe_one, blockSumAddEquiv_apply, χ₀,
      upperPart_add_of_mem B q.1.2 q.2.2, lowerPart_add_of_mem B q.1.2 q.2.2]
    noncomm_ring
  have hmeas_g : Measurable (fun q : (parabolicSubalgebra (R := 𝕂) B) × (lowerLie (E := 𝕂) B) =>
      (q.1 : Matrix (Fin n) (Fin n) 𝕂) * (1 + q.2)) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))).measurable
  have hmeas_t : Measurable (fun W : parabolicSubalgebra (R := 𝕂) B => one + W) :=
    (continuous_const.add continuous_id).measurable
  have hmeas_χ : Measurable χ₀ :=
    (continuous_id.add ((continuous_upperPart B).mul (continuous_lowerPart B))).measurable
  have hmeas_e : Measurable (blockSumAddEquiv (𝕂 := 𝕂) B) :=
    (blockSumHomeomorph (𝕂 := 𝕂) B).measurable
  have hmeas_1 : Measurable (fun X : Matrix (Fin n) (Fin n) 𝕂 => 1 + X) :=
    (continuous_const.add continuous_id).measurable
  rw [htrS, ← Measure.map_id (μ := νL.restrict _), Measure.map_prod_map _ _ hmeas_t
    measurable_id, Measure.map_map hmeas_g (hmeas_t.prodMap measurable_id), hfun,
    ← Measure.map_map hmeas_1 (hmeas_χ.comp hmeas_e),
    ← Measure.map_map hmeas_χ hmeas_e, ← blockSumMeasure_restrict_closedBall_zero]
  change Measure.map (fun X => 1 + X) (Measure.map χ₀ (ν.restrict (closedBall 0 r))) = _
  rw [hχ₀, htr]

end Coordinates

end Langlands.BaseChange.TwistedLocalDescent
