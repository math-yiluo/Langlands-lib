import Langlands.BaseChange.TwistedLocalDescent.MassChart

/-! # The mass identity for the twisted orbital kernel

Assembling the Iwahori reduction, the restriction to `d (P ∩ K(r))`, the additive coordinates on
`P ∩ K(r)` and on `K(r)`, and the change of variables through the twisted chart, over an ultrametric
proper nontrivially normed field with an isometric `σ`: `∫_K Φ = δh(d) c ∫_G φ`, where `c` is the
factor by which the linear part `A` of the chart at `d` scales additive Haar measure. The hypotheses
(those of `integral_twistedOrbitalKernel_eq_mass`) are: `dg = dp dk` with `dg` right invariant and
`θP` preserving `dp`; `Q` measurable and stable under twisted conjugation; `δh` continuous,
multiplicative, invariant under twisted conjugation and trivial on `P ∩ K(r)`; `φ` continuous,
compactly supported and bi-invariant under an open subgroup; `K(r)` a compact congruence subgroup of
radius `0 < r < 1`; a bound `‖A⁻¹ Y‖ ≤ C ‖Y‖` with `C max(‖d⁻¹‖ ‖d‖, 1) r < 1`; chart support of
`φ(x · θ(x)⁻¹)`; pointwise rigidity; and `d (P ∩ K(r)) ⊆ Q`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe v

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace matrix_locallyCompactSpace
  parabolicSubalgebra_locallyCompact parabolicSubalgebra_isTopologicalRing
  lowerLie_locallyCompact matrix_secondCountable lowerLie_secondCountable
  parabolicSubalgebra_secondCountable

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} (B : BlockShape n) (σ : 𝕂 →+* 𝕂)
  [MeasurableSpace (GeneralLinear n 𝕂)] [BorelSpace (GeneralLinear n 𝕂)]
  [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)]

omit [MeasurableSpace (GeneralLinear n 𝕂)]
  [BorelSpace (GeneralLinear n 𝕂)] [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)]
  [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)] in
theorem isOpenEmbedding_val_generalLinear :
    IsOpenEmbedding (fun g : GeneralLinear n 𝕂 => g.val) := Units.isOpenEmbedding_val

/-- **Additive coordinates on `P ∩ K(r)` inside the twisted orbital kernel.** -/
theorem integral_parabolic_congruence_eq (d : B.parabolic 𝕂)
    (U : OpenSubgroup (GeneralLinear n 𝕂)) (hUc : IsCompact (U : Set (GeneralLinear n 𝕂)))
    {r : ℝ} (hr0 : 0 < r)
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    (μP : Measure (B.parabolic 𝕂)) [μP.IsHaarMeasure]
    (νS : Measure (parabolicSubalgebra (R := 𝕂) B)) [νS.IsAddHaarMeasure]
    (φx : GeneralLinear n 𝕂 → ℂ) (hφxc : Continuous φx) (hφxs : HasCompactSupport φx)
    (Z : lowerLie (E := 𝕂) B) :
    ∫ h, {h : B.parabolic 𝕂 | (h : GeneralLinear n 𝕂) ∈ U}.indicator
        (fun h : B.parabolic 𝕂 => φx ((lowerUnit B Z)⁻¹ * d * h *
          Matrix.GeneralLinearGroup.map σ (lowerUnit B Z))) h ∂μP =
      ((μP {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U} *
        (νS (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r))⁻¹).toReal : ℂ) *
        ∫ W, Function.extend (fun g : GeneralLinear n 𝕂 => g.val) φx 0
          (lowerInverse B (Z : Matrix (Fin n) (Fin n) 𝕂) * (d : GeneralLinear n 𝕂).val *
            (W : Matrix (Fin n) (Fin n) 𝕂) * (1 + (Z : Matrix (Fin n) (Fin n) 𝕂)).map σ)
          ∂(νS.restrict (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r)) := by
  set φt := Function.extend (fun g : GeneralLinear n 𝕂 => g.val) φx 0
  have hemb := isOpenEmbedding_val_generalLinear (𝕂 := 𝕂) (n := n)
  have hφtc : Continuous φt := continuous_extend_zero_of_isOpenEmbedding hemb hφxc hφxs
  set F : Matrix (Fin n) (Fin n) 𝕂 → ℂ := fun X => φt (lowerInverse B (Z : Matrix (Fin n) (Fin n) 𝕂) *
    (d : GeneralLinear n 𝕂).val * X * (1 + (Z : Matrix (Fin n) (Fin n) 𝕂)).map σ)
  have hFc : Continuous F :=
    hφtc.comp (((continuous_const.mul continuous_const).mul continuous_id).mul continuous_const)
  have hval : ∀ h : B.parabolic 𝕂, φx ((lowerUnit B Z)⁻¹ * d * h *
      Matrix.GeneralLinearGroup.map σ (lowerUnit B Z)) = F (h : GeneralLinear n 𝕂).val := by
    intro h
    simp only [F, φt]
    rw [← val_twistedConj_lowerUnit, extend_zero_apply_of_injective hemb.injective]
  have hHmeas : MeasurableSet {h : B.parabolic 𝕂 | (h : GeneralLinear n 𝕂) ∈ U} :=
    (U.isOpen.preimage continuous_subtype_val).measurableSet
  simp_rw [hval]
  rw [integral_indicator hHmeas]
  have hC := map_val_restrict_parabolic_congruenceBall B μP νS U hUc hr0 hU hrange
  have hmP : Measurable (fun p : B.parabolic 𝕂 => (p : GeneralLinear n 𝕂).val) :=
    (Units.continuous_val.comp continuous_subtype_val).measurable
  have h1 : ∫ h in {h : B.parabolic 𝕂 | (h : GeneralLinear n 𝕂) ∈ U},
      F (h : GeneralLinear n 𝕂).val ∂μP =
      ∫ X, F X ∂((μP.restrict {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U}).map
        (fun p : B.parabolic 𝕂 => (p : GeneralLinear n 𝕂).val)) :=
    (integral_map hmP.aemeasurable hFc.aestronglyMeasurable).symm
  rw [h1, hC, integral_smul_measure, integral_map continuous_subtype_val.measurable.aemeasurable
    hFc.aestronglyMeasurable, Complex.real_smul]

omit [MeasurableSpace (GeneralLinear n 𝕂)] [BorelSpace (GeneralLinear n 𝕂)] in
/-- **Fubini and the chart.** The iterated integral over the balls of `𝔭` and `𝔲̄` is the
integral over the image of the ball under the linear part of the chart, scaled by `c`. -/
theorem integral_balls_eq_chart (hσc : Continuous σ) (d : GeneralLinear n 𝕂)
    (νS : Measure (parabolicSubalgebra (R := 𝕂) B)) [νS.IsAddHaarMeasure]
    (νL : Measure (lowerLie (E := 𝕂) B)) [νL.IsAddHaarMeasure] {r : ℝ}
    (A : Matrix (Fin n) (Fin n) 𝕂 ≃ₜ+ Matrix (Fin n) (Fin n) 𝕂) (c : ℝ≥0∞)
    (hchart : ((blockSumMeasure B νS νL).restrict (closedBall 0 r)).map
      (twistedChart B σ d.val (d⁻¹).val) = c • (blockSumMeasure B νS νL).restrict
        (A '' closedBall 0 r))
    (φt : Matrix (Fin n) (Fin n) 𝕂 → ℂ) (hφtc : Continuous φt) {Cφ : ℝ}
    (hφtb : ∀ X, ‖φt X‖ ≤ Cφ) :
    ∫ Z, (∫ W, φt (lowerInverse B (Z : Matrix (Fin n) (Fin n) 𝕂) * d.val *
        (W : Matrix (Fin n) (Fin n) 𝕂) * (1 + (Z : Matrix (Fin n) (Fin n) 𝕂)).map σ)
        ∂(νS.restrict (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r)))
        ∂(νL.restrict (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)) =
      (c.toReal : ℂ) * ∫ Y in A '' closedBall 0 r, φt (d.val * (1 + Y))
        ∂(blockSumMeasure B νS νL) := by
  set ν := blockSumMeasure B νS νL
  set RS : Set (parabolicSubalgebra (R := 𝕂) B) :=
    Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r
  set BS0 : Set (parabolicSubalgebra (R := 𝕂) B) :=
    Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r
  set RL : Set (lowerLie (E := 𝕂) B) :=
    Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r
  have hS_closed := isClosed_parabolicSubalgebra (𝕂 := 𝕂) B
  have hL_closed := isClosed_lowerLie (𝕂 := 𝕂) B
  have : IsFiniteMeasure (νS.restrict RS) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (hS_closed.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall _ _)).measure_lt_top⟩
  have : IsFiniteMeasure (νS.restrict BS0) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (hS_closed.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall _ _)).measure_lt_top⟩
  have : IsFiniteMeasure (νL.restrict RL) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (hL_closed.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall _ _)).measure_lt_top⟩
  set f : parabolicSubalgebra (R := 𝕂) B × lowerLie (E := 𝕂) B → ℂ := fun q =>
    φt (lowerInverse B (q.2 : Matrix (Fin n) (Fin n) 𝕂) * d.val *
      (q.1 : Matrix (Fin n) (Fin n) 𝕂) * (1 + (q.2 : Matrix (Fin n) (Fin n) 𝕂)).map σ)
  have hfc : Continuous f := by
    refine hφtc.comp ?_
    refine ((((continuous_lowerInverse B).comp (continuous_subtype_val.comp continuous_snd)).mul
      continuous_const).mul (continuous_subtype_val.comp continuous_fst)).mul ?_
    exact (continuous_matrix_map σ hσc).comp
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))
  have hint : Integrable f ((νS.restrict RS).prod (νL.restrict RL)) :=
    Integrable.of_bound hfc.aestronglyMeasurable Cφ (Filter.Eventually.of_forall fun q => hφtb _)
  have h1 : ∫ Z, (∫ W, f (W, Z) ∂(νS.restrict RS)) ∂(νL.restrict RL) =
      ∫ q, f q ∂((νS.restrict RS).prod (νL.restrict RL)) := (integral_prod_symm f hint).symm
  change ∫ Z, (∫ W, f (W, Z) ∂(νS.restrict RS)) ∂(νL.restrict RL) = _
  rw [h1]
  -- translate the `𝔭`-ball to the origin
  have ht : Measurable (fun W : parabolicSubalgebra (R := 𝕂) B =>
      (1 : parabolicSubalgebra (R := 𝕂) B) + W) := (continuous_const.add continuous_id).measurable
  rw [show νS.restrict RS = (νS.restrict BS0).map
      (fun W => (1 : parabolicSubalgebra (R := 𝕂) B) + W) from
      restrict_closedBall_one_eq_map B νS r,
    ← Measure.map_id (μ := νL.restrict RL), Measure.map_prod_map _ _ ht measurable_id,
    integral_map (ht.prodMap measurable_id).aemeasurable hfc.aestronglyMeasurable]
  -- the chart
  set G : Matrix (Fin n) (Fin n) 𝕂 → ℂ := fun X =>
    φt (d.val * (1 + twistedChart B σ d.val (d⁻¹).val X))
  have hd1 : d.val * (d⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGc : Continuous G :=
    hφtc.comp (continuous_const.mul (continuous_const.add
      (continuous_twistedChart B σ d.val (d⁻¹).val hσc)))
  have hfG : ∀ q : parabolicSubalgebra (R := 𝕂) B × lowerLie (E := 𝕂) B,
      f (Prod.map (fun W => (1 : parabolicSubalgebra (R := 𝕂) B) + W) id q) =
        G (blockSumAddEquiv B q) := by
    intro q
    simp only [f, G, Prod.map_fst, Prod.map_snd, id_eq, blockSumAddEquiv_apply,
      mul_one_add_twistedChart B σ _ _ hd1, upperPart_add_of_mem B q.1.2 q.2.2,
      lowerPart_add_of_mem B q.1.2 q.2.2, Subalgebra.coe_add, OneMemClass.coe_one]
  simp_rw [hfG]
  have he : Measurable (blockSumAddEquiv (𝕂 := 𝕂) B) :=
    (blockSumHomeomorph (𝕂 := 𝕂) B).measurable
  rw [← integral_map he.aemeasurable hGc.aestronglyMeasurable,
    ← blockSumMeasure_restrict_closedBall_zero B νS νL r]
  have hχm : Measurable (twistedChart B σ d.val (d⁻¹).val) :=
    (continuous_twistedChart B σ d.val (d⁻¹).val hσc).measurable
  have hφ1 : Continuous fun Y : Matrix (Fin n) (Fin n) 𝕂 => φt (d.val * (1 + Y)) :=
    hφtc.comp (continuous_const.mul (continuous_const.add continuous_id))
  change ∫ X, (fun Y => φt (d.val * (1 + Y))) (twistedChart B σ d.val (d⁻¹).val X)
    ∂(ν.restrict (closedBall 0 r)) = _
  rw [← integral_map hχm.aemeasurable hφ1.aestronglyMeasurable, hchart, integral_smul_measure,
    Complex.real_smul]

/-- **The integral of `φ` in the coordinates at `d`.** -/
theorem integral_eq_chart_coordinates (d : GeneralLinear n 𝕂)
    (U : OpenSubgroup (GeneralLinear n 𝕂)) (hUc : IsCompact (U : Set (GeneralLinear n 𝕂)))
    {r : ℝ}
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    (μG : Measure (GeneralLinear n 𝕂)) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (ν : Measure (Matrix (Fin n) (Fin n) 𝕂)) [ν.IsAddHaarMeasure]
    (A : Matrix (Fin n) (Fin n) 𝕂 ≃ₜ+ Matrix (Fin n) (Fin n) 𝕂)
    (φ : GeneralLinear n 𝕂 → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : GeneralLinear n 𝕂)
    (hsupp : ∀ y : GeneralLinear n 𝕂,
      φ (x * y * (Matrix.GeneralLinearGroup.map σ x)⁻¹) ≠ 0 →
        ∃ Y, Y ∈ A '' closedBall 0 r ∧ ‖Y‖ ≤ r ∧ y.val = d.val * (1 + Y)) :
    ∫ g, φ g ∂μG = ((μG U * (ν (closedBall 1 r))⁻¹).toReal : ℂ) *
      ∫ Y in A '' closedBall 0 r, Function.extend (fun g : GeneralLinear n 𝕂 => g.val)
        (fun y => φ (x * y * (Matrix.GeneralLinearGroup.map σ x)⁻¹)) 0 (d.val * (1 + Y)) ∂ν := by
  set θ := Matrix.GeneralLinearGroup.map (n := Fin n) σ
  set φx : GeneralLinear n 𝕂 → ℂ := fun y => φ (x * y * (θ x)⁻¹)
  set φt := Function.extend (fun g : GeneralLinear n 𝕂 => g.val) φx 0
  have hemb := isOpenEmbedding_val_generalLinear (𝕂 := 𝕂) (n := n)
  have hφxc : Continuous φx := hφc.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hφxs : HasCompactSupport φx := by
    have : φx = φ ∘ ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight (θ x)⁻¹)) := by
      funext y
      rfl
    rw [this]
    exact hφs.comp_homeomorph _
  have hφtc : Continuous φt := continuous_extend_zero_of_isOpenEmbedding hemb hφxc hφxs
  have hφt_val : ∀ g : GeneralLinear n 𝕂, φt g.val = φx g :=
    extend_zero_apply_of_injective hemb.injective φx
  have hcancel : ∀ M M' : Matrix (Fin n) (Fin n) 𝕂, d.val * M = d.val * M' → M = M' := by
    intro M M' h
    have := congrArg (fun X => (d⁻¹).val * X) h
    simpa only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] using this
  -- `∫ φ = ∫ φx = ∫ φx(d ·)`
  have h1 : ∫ g, φ g ∂μG = ∫ y, φx (d * y) ∂μG := by
    rw [integral_mul_left_eq_self φx d]
    change _ = ∫ y, φ (x * y * (θ x)⁻¹) ∂μG
    rw [show (fun y => φ (x * y * (θ x)⁻¹)) = fun y => (fun z => φ (z * (θ x)⁻¹)) (x * y) from rfl,
      integral_mul_left_eq_self (fun z => φ (z * (θ x)⁻¹)) x,
      integral_mul_right_eq_self φ (θ x)⁻¹]
  -- restriction to `U`
  have hUmeas : MeasurableSet (U : Set (GeneralLinear n 𝕂)) := U.isOpen.measurableSet
  have h2 : ∫ y, φx (d * y) ∂μG = ∫ y in (U : Set (GeneralLinear n 𝕂)), φx (d * y) ∂μG := by
    rw [← integral_indicator hUmeas]
    congr 1
    funext y
    by_cases hy : φx (d * y) = 0
    · rw [hy]
      by_cases hyU : y ∈ (U : Set (GeneralLinear n 𝕂))
      · rw [Set.indicator_of_mem hyU, hy]
      · rw [Set.indicator_of_notMem hyU]
    · obtain ⟨Y, -, hY, hyY⟩ := hsupp (d * y) hy
      have hyU : y ∈ (U : Set (GeneralLinear n 𝕂)) := by
        rw [hU]
        have : y.val = 1 + Y := hcancel _ _ (by rw [← hyY, Units.val_mul])
        change y.val - 1 ∈ closedBall 0 r
        rw [this, add_sub_cancel_left, mem_closedBall_zero_iff]
        exact hY
      rw [Set.indicator_of_mem hyU]
  -- Haar measure on `U` in additive coordinates
  have : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  have hA := map_val_restrict_congruenceBall μG ν U hrange
  have hval : Measurable (fun g : GeneralLinear n 𝕂 => g.val) := Units.continuous_val.measurable
  have hF : Continuous fun X : Matrix (Fin n) (Fin n) 𝕂 => φt (d.val * X) :=
    hφtc.comp (continuous_const.mul continuous_id)
  have h3 : ∫ y in (U : Set (GeneralLinear n 𝕂)), φx (d * y) ∂μG =
      ((μG U * (ν (closedBall 1 r))⁻¹).toReal : ℂ) *
        ∫ X in closedBall 1 r, φt (d.val * X) ∂ν := by
    have hpt : ∀ y : GeneralLinear n 𝕂, φx (d * y) = φt (d.val * y.val) := by
      intro y
      rw [← hφt_val, Units.val_mul]
    simp_rw [hpt]
    change ∫ y, (fun X => φt (d.val * X)) y.val ∂(μG.restrict (U : Set (GeneralLinear n 𝕂))) = _
    rw [← integral_map hval.aemeasurable hF.aestronglyMeasurable]
    change ∫ X, φt (d.val * X) ∂(Measure.map Units.val
      (μG.restrict (U : Set (GeneralLinear n 𝕂)))) = _
    rw [hA, integral_smul_measure, Complex.real_smul]
  -- translate to the origin
  have h4 : ∫ X in closedBall 1 r, φt (d.val * X) ∂ν =
      ∫ Y in closedBall 0 r, φt (d.val * (1 + Y)) ∂ν := by
    have h1m : Measurable (fun X : Matrix (Fin n) (Fin n) 𝕂 => 1 + X) :=
      (continuous_const.add continuous_id).measurable
    rw [← map_one_add_restrict_closedBall_zero ν r,
      integral_map h1m.aemeasurable hF.aestronglyMeasurable]
  -- the integrand vanishes outside `A(ball) ∩ ball`
  have hmA : MeasurableSet (A '' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r) :=
    ((isCompact_closedBall _ _).image A.continuous).isClosed.measurableSet
  have h5 : ∫ Y in closedBall 0 r, φt (d.val * (1 + Y)) ∂ν =
      ∫ Y in A '' closedBall 0 r, φt (d.val * (1 + Y)) ∂ν := by
    have hcl : IsClosed (closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r) := isClosed_closedBall
    rw [← integral_indicator hcl.measurableSet, ← integral_indicator hmA]
    congr 1
    funext Y
    by_cases hY : φt (d.val * (1 + Y)) = 0
    · by_cases h1 : Y ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r
      · rw [Set.indicator_of_mem h1, hY]
        by_cases h2 : Y ∈ A '' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r
        · rw [Set.indicator_of_mem h2, hY]
        · rw [Set.indicator_of_notMem h2]
      · rw [Set.indicator_of_notMem h1]
        by_cases h2 : Y ∈ A '' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r
        · rw [Set.indicator_of_mem h2, hY]
        · rw [Set.indicator_of_notMem h2]
    · obtain ⟨y, hyv, hy⟩ := exists_eq_of_extend_zero_ne hemb.injective hY
      obtain ⟨Y', hY'A, hY'r, hyY'⟩ := hsupp y hy
      have hYY : Y = Y' := by
        have := hcancel _ _ (hyv.symm.trans hyY')
        exact add_left_cancel this
      subst hYY
      rw [Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hY'r), Set.indicator_of_mem hY'A]
  rw [h1, h2, h3, h4, h5]

/-- **The mass identity.** Under the hypotheses listed in the module docstring (Iwasawa
decomposition, invariance of `Q` and `δh`, multiplicativity of `δh` and its triviality on
`P ∩ U`, regularity of `φ`, the smallness condition, chart support of `φ(x · θ(x)⁻¹)`, rigidity
and `d (P ∩ U) ⊆ Q`), the integral over `K` of the twisted orbital kernel is `δh(d) c ∫_G φ`,
where `c` is the Haar scaling factor of the linear part `A` of the twisted chart at `d`. -/
theorem integral_twistedOrbitalKernel_eq_mass (hσ : ∀ a, ‖σ a‖ = ‖a‖)
    (θP : B.parabolic 𝕂 →* B.parabolic 𝕂)
    (hθP : ∀ p, (θP p : GeneralLinear n 𝕂) = Matrix.GeneralLinearGroup.map σ p)
    (hθPm : Measurable θP)
    (μG : Measure (GeneralLinear n 𝕂)) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (μP : Measure (B.parabolic 𝕂)) [μP.IsHaarMeasure] (hμPθ : μP.map θP = μP)
    (K : Subgroup (GeneralLinear n 𝕂)) [CompactSpace K] (μK : Measure K) [IsFiniteMeasure μK]
    (hIw : μG = (μP.prod μK).map (fun y => (y.1 : GeneralLinear n 𝕂) * y.2))
    (Q : Set (B.parabolic 𝕂)) (hQ : MeasurableSet Q)
    (hQinv : ∀ h p, p ∈ Q → h * p * (θP h)⁻¹ ∈ Q)
    (δh : B.parabolic 𝕂 → ℝ) (hδc : Continuous δh)
    (hδinv : ∀ h p, δh (h * p * (θP h)⁻¹) = δh p) (hδmul : ∀ a b, δh (a * b) = δh a * δh b)
    (φ : GeneralLinear n 𝕂 → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (V : Subgroup (GeneralLinear n 𝕂)) (hVo : IsOpen (V : Set (GeneralLinear n 𝕂)))
    (hφV : ∀ v ∈ V, ∀ v' ∈ V, ∀ g, φ (v * g * v') = φ g)
    (νS : Measure (parabolicSubalgebra (R := 𝕂) B)) [νS.IsAddHaarMeasure]
    (νL : Measure (lowerLie (E := 𝕂) B)) [νL.IsAddHaarMeasure]
    (U : OpenSubgroup (GeneralLinear n 𝕂)) (hUc : IsCompact (U : Set (GeneralLinear n 𝕂)))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    (hδW : ∀ h : B.parabolic 𝕂, (h : GeneralLinear n 𝕂) ∈ U → δh h = 1)
    (d : B.parabolic 𝕂) (x : GeneralLinear n 𝕂)
    (A : Matrix (Fin n) (Fin n) 𝕂 ≃ₜ+ Matrix (Fin n) (Fin n) 𝕂)
    (hAlin : ∀ X, A X = twistedChartLinear B σ (d : GeneralLinear n 𝕂).val
      ((d : GeneralLinear n 𝕂)⁻¹).val X)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ Y, ‖A.symm Y‖ ≤ C * ‖Y‖) (c : ℝ≥0∞)
    (hA : (blockSumMeasure B νS νL).map A = c • blockSumMeasure B νS νL)
    (hsmall : C * (max (‖((d : GeneralLinear n 𝕂)⁻¹).val‖ * ‖(d : GeneralLinear n 𝕂).val‖) 1 *
      r) < 1)
    (hsupp : ∀ y : GeneralLinear n 𝕂,
      φ (x * y * (Matrix.GeneralLinearGroup.map σ x)⁻¹) ≠ 0 →
        ∃ Y, Y ∈ A '' closedBall 0 r ∧ ‖Y‖ ≤ r ∧
          y.val = (d : GeneralLinear n 𝕂).val * (1 + Y))
    (hrig : ∀ (g : GeneralLinear n 𝕂) (p h : B.parabolic 𝕂), p ∈ Q →
      (h : GeneralLinear n 𝕂) ∈ U →
      g * p * (Matrix.GeneralLinearGroup.map σ g)⁻¹ = d * h → g ∈ B.parabolic 𝕂)
    (hdQ : ∀ h : B.parabolic 𝕂, (h : GeneralLinear n 𝕂) ∈ U → d * h ∈ Q) :
    ∫ k, twistedOrbitalKernel (Matrix.GeneralLinearGroup.map σ) μP Q δh φ k ∂μK =
      ((δh d : ℂ) * (c.toReal : ℂ)) * ∫ g, φ g ∂μG := by
  set θ := Matrix.GeneralLinearGroup.map (n := Fin n) σ
  set ν := blockSumMeasure B νS νL
  have hσc : Continuous σ := by
    refine continuous_iff_continuousAt.mpr fun a => ?_
    rw [ContinuousAt, Metric.tendsto_nhds_nhds]
    intro ε hε
    refine ⟨ε, hε, fun b hb => ?_⟩
    rw [dist_eq_norm, ← map_sub, hσ, ← dist_eq_norm]
    exact hb
  have hθc : Continuous θ := by
    rw [Units.continuous_iff]
    refine ⟨(continuous_matrix_map σ hσc).comp Units.continuous_val, ?_⟩
    exact (continuous_matrix_map σ hσc).comp
      (Units.continuous_val.comp (continuous_inv (G := GeneralLinear n 𝕂)))
  have hdinv : ((d : GeneralLinear n 𝕂)⁻¹).val * (d : GeneralLinear n 𝕂).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨hchart, himg⟩ := map_restrict_closedBall_twistedChart B σ (d : GeneralLinear n 𝕂).val
    ((d : GeneralLinear n 𝕂)⁻¹).val hσ hdinv ν A hAlin hC0 hC c hA hr0 hr1.le hsmall
  -- the reduction to the opposite unipotent ball
  have hred := integral_twistedOrbitalKernel_eq_iwahori B θ hθc θP hθP hθPm μG μP hμPθ K μK hIw
    Q hQ hQinv δh hδc hδinv φ hφc V hVo hφV νS νL U hUc hr0 hr1 hU hrange x
    (fun k hk => rel_of_twistedOrbitalKernel_ne_zero B σ d U hU hrange A himg μP Q δh φ x hsupp
      hrig k hk)
  rw [hred]
  -- the integrand on the ball
  set φx : GeneralLinear n 𝕂 → ℂ := fun y => φ (x * y * (θ x)⁻¹)
  set φt := Function.extend (fun g : GeneralLinear n 𝕂 => g.val) φx 0
  have hemb := isOpenEmbedding_val_generalLinear (𝕂 := 𝕂) (n := n)
  have hφxc : Continuous φx := hφc.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hφxs : HasCompactSupport φx := by
    have : φx = φ ∘ ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight (θ x)⁻¹)) := by
      funext y
      rfl
    rw [this]
    exact hφs.comp_homeomorph _
  have hφtc : Continuous φt := continuous_extend_zero_of_isOpenEmbedding hemb hφxc hφxs
  obtain ⟨Cφ, hCφ⟩ := hφxc.bounded_above_of_compact_support hφxs
  have hφtb : ∀ X, ‖φt X‖ ≤ Cφ := by
    intro X
    by_cases hX : ∃ g : GeneralLinear n 𝕂, g.val = X
    · obtain ⟨g, rfl⟩ := hX
      change ‖Function.extend (fun g : GeneralLinear n 𝕂 => g.val) φx 0 g.val‖ ≤ Cφ
      rw [extend_zero_apply_of_injective hemb.injective]
      exact hCφ g
    · change ‖Function.extend (fun g : GeneralLinear n 𝕂 => g.val) φx 0 X‖ ≤ Cφ
      rw [Function.extend_apply' (f := fun g : GeneralLinear n 𝕂 => g.val) φx
        (0 : Matrix (Fin n) (Fin n) 𝕂 → ℂ) X hX, Pi.zero_apply, norm_zero]
      exact (norm_nonneg _).trans (hCφ 1)
  set b := μP {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U} *
    (νS (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r))⁻¹
  have hpt : ∀ Z : lowerLie (E := 𝕂) B,
      twistedOrbitalKernel θ μP Q δh φ (lowerUnit B Z * x⁻¹) =
        (δh d : ℂ) * ((b.toReal : ℂ) * ∫ W, φt (lowerInverse B (Z : Matrix (Fin n) (Fin n) 𝕂) *
          (d : GeneralLinear n 𝕂).val * (W : Matrix (Fin n) (Fin n) 𝕂) *
            (1 + (Z : Matrix (Fin n) (Fin n) 𝕂)).map σ)
          ∂(νS.restrict (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r))) := by
    intro Z
    rw [twistedOrbitalKernel_lowerUnit_mul_inv B σ d U hrange A himg μP Q δh hδmul hδW hdQ φ x
      hsupp hrig Z]
    congr 1
    exact integral_parabolic_congruence_eq B σ d U hUc hr0 hU hrange μP νS φx hφxc hφxs Z
  simp_rw [hpt]
  rw [integral_const_mul, integral_const_mul,
    integral_balls_eq_chart B σ hσc (d : GeneralLinear n 𝕂) νS νL A c hchart φt hφtc hφtb,
    integral_eq_chart_coordinates σ (d : GeneralLinear n 𝕂) U hUc hU hrange μG ν A φ hφc hφs x
      hsupp]
  -- the constants
  have hS_closed := isClosed_parabolicSubalgebra (𝕂 := 𝕂) B
  have hRS_open : IsOpen (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r :
      Set (parabolicSubalgebra (R := 𝕂) B)) :=
    (IsUltrametricDist.isOpen_closedBall _ hr0.ne').preimage continuous_subtype_val
  have hRS_compact : IsCompact (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r :
      Set (parabolicSubalgebra (R := 𝕂) B)) :=
    hS_closed.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall _ _)
  have hRS_ne : (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r :
      Set (parabolicSubalgebra (R := 𝕂) B)).Nonempty := ⟨1, by
    change (1 : Matrix (Fin n) (Fin n) 𝕂) ∈ closedBall 1 r
    exact mem_closedBall_self hr0.le⟩
  have hPcl := isClosed_parabolic_of_normed (𝕂 := 𝕂) B
  have hs_open : IsOpen {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U} :=
    U.isOpen.preimage continuous_subtype_val
  have hs_compact : IsCompact {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U} :=
    hPcl.isClosedEmbedding_subtypeVal.isCompact_preimage hUc
  have : LocallyCompactSpace (B.parabolic 𝕂) :=
    hPcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hb0 : b ≠ 0 :=
    mul_ne_zero (hs_open.measure_pos μP ⟨1, U.one_mem⟩).ne'
      (ENNReal.inv_ne_zero.mpr hRS_compact.measure_lt_top.ne)
  have hbtop : b ≠ ⊤ :=
    ENNReal.mul_ne_top hs_compact.measure_lt_top.ne
      (ENNReal.inv_ne_top.mpr (hRS_open.measure_pos νS hRS_ne).ne')
  have hab : (iwahoriConstant B μG μP νS νL U r).toReal * b.toReal =
      (μG U * (ν (closedBall 1 r))⁻¹).toReal := by
    rw [← ENNReal.toReal_mul, iwahoriConstant, ENNReal.div_mul_cancel hb0 hbtop]
  have habC : ((iwahoriConstant B μG μP νS νL U r).toReal : ℂ) * (b.toReal : ℂ) =
      ((μG U * (ν (closedBall 1 r))⁻¹).toReal : ℂ) := by
    rw [← Complex.ofReal_mul, hab]
  linear_combination (↑(δh d) * ↑c.toReal *
    ∫ Y in A '' closedBall 0 r, φt ((d : GeneralLinear n 𝕂).val * (1 + Y)) ∂ν) * habC

end Langlands.BaseChange.TwistedLocalDescent
