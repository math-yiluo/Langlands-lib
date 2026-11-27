import Langlands.BaseChange.TwistedLocalDescent.Iwahori
import Langlands.BaseChange.TwistedLocalDescent.HaarRestrict

/-! # The Iwahori factorization of Haar measure on a congruence subgroup of `GL_n`

Over an ultrametric proper nontrivially normed field, for a compact congruence subgroup
`U = {g : ‖g − 1‖ ≤ r}` with `0 < r < 1`, Haar measure of `GL_n` restricted to `U` is a constant
multiple of the image of `(Haar measure of P restricted to P ∩ U) × (additive Haar measure of 𝔲̄
restricted to the ball of radius r)` under `(p, Z) ↦ p (1 + Z)`. See the paired Markdown.
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
  {n : ℕ} (B : BlockShape n)
  [MeasurableSpace (GeneralLinear n 𝕂)] [BorelSpace (GeneralLinear n 𝕂)]
  [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)]

/-- The constant of the Iwahori factorization. -/
def iwahoriConstant (μG : Measure (GeneralLinear n 𝕂)) (μP : Measure (B.parabolic 𝕂))
    (νS : Measure (parabolicSubalgebra (R := 𝕂) B)) (νL : Measure (lowerLie (E := 𝕂) B))
    (U : OpenSubgroup (GeneralLinear n 𝕂)) (r : ℝ) : ℝ≥0∞ :=
  μG U * (blockSumMeasure B νS νL (closedBall 1 r))⁻¹ /
    (μP {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U} *
      (νS (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r))⁻¹)

/-- **Iwahori factorization of Haar measure on a congruence subgroup.** -/
theorem restrict_congruenceBall_eq_map_mul_lowerUnit (μG : Measure (GeneralLinear n 𝕂))
    [μG.IsHaarMeasure] (μP : Measure (B.parabolic 𝕂)) [μP.IsHaarMeasure]
    (νS : Measure (parabolicSubalgebra (R := 𝕂) B)) [νS.IsAddHaarMeasure]
    (νL : Measure (lowerLie (E := 𝕂) B)) [νL.IsAddHaarMeasure]
    (U : OpenSubgroup (GeneralLinear n 𝕂)) (hUc : IsCompact (U : Set (GeneralLinear n 𝕂)))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r) :
    μG.restrict (U : Set (GeneralLinear n 𝕂)) =
      iwahoriConstant B μG μP νS νL U r •
        ((μP.restrict {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U}).prod
          (νL.restrict (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r))).map
          (fun q => (q.1 : GeneralLinear n 𝕂) * lowerUnit B q.2) := by
  set s := {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U}
  set RS : Set (parabolicSubalgebra (R := 𝕂) B) :=
    Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r with hRS
  set RL : Set (lowerLie (E := 𝕂) B) :=
    Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r
  set ν := blockSumMeasure B νS νL
  have : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  have : SecondCountableTopology (GeneralLinear n 𝕂) :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (B.parabolic 𝕂) :=
    inferInstanceAs (SecondCountableTopology ((B.parabolic 𝕂) : Set (GeneralLinear n 𝕂)))
  have hvalo : IsOpenEmbedding (fun g : GeneralLinear n 𝕂 => g.val) := Units.isOpenEmbedding_val
  have hval : MeasurableEmbedding (fun g : GeneralLinear n 𝕂 => g.val) :=
    hvalo.measurableEmbedding
  -- the constant `b` of the parabolic
  have hS_closed := isClosed_parabolicSubalgebra (𝕂 := 𝕂) B
  have hRS_open : IsOpen RS :=
    (IsUltrametricDist.isOpen_closedBall _ hr0.ne').preimage continuous_subtype_val
  have hRS_compact : IsCompact RS :=
    hS_closed.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall _ _)
  have hRS_ne : RS.Nonempty := ⟨1, by
    change (1 : Matrix (Fin n) (Fin n) 𝕂) ∈ closedBall 1 r
    exact mem_closedBall_self hr0.le⟩
  have hs_open : IsOpen s := U.isOpen.preimage continuous_subtype_val
  have hs_compact : IsCompact s :=
    (isClosed_parabolic_of_normed B).isClosedEmbedding_subtypeVal.isCompact_preimage hUc
  have hs_ne : s.Nonempty := ⟨1, U.one_mem⟩
  have hb0 : μP s * (νS RS)⁻¹ ≠ 0 :=
    mul_ne_zero (hs_open.measure_pos μP hs_ne).ne'
      (ENNReal.inv_ne_zero.mpr hRS_compact.measure_lt_top.ne)
  have hbtop : μP s * (νS RS)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top hs_compact.measure_lt_top.ne
      (ENNReal.inv_ne_top.mpr (hRS_open.measure_pos νS hRS_ne).ne')
  have hA := map_val_restrict_congruenceBall μG ν U hrange
  have hC := map_val_restrict_parabolic_congruenceBall B μP νS U hUc hr0 hU hrange
  have hI := map_mul_one_add_restrict B νS νL hr0 hr1
  -- compare after pushing forward along `Units.val`
  rw [← hval.comap_map (μ := μG.restrict _), hA]
  have hmulL : Measurable (fun q : B.parabolic 𝕂 × lowerLie (E := 𝕂) B =>
      (q.1 : GeneralLinear n 𝕂) * lowerUnit B q.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_lowerUnit B).comp continuous_snd)).measurable
  have hmP : Measurable (fun p : B.parabolic 𝕂 => (p : GeneralLinear n 𝕂).val) :=
    (Units.continuous_val.comp continuous_subtype_val).measurable
  have hg : Measurable (fun q : Matrix (Fin n) (Fin n) 𝕂 × lowerLie (E := 𝕂) B =>
      q.1 * (1 + (q.2 : Matrix (Fin n) (Fin n) 𝕂))) :=
    (continuous_fst.mul (continuous_const.add (continuous_subtype_val.comp continuous_snd))).measurable
  have hgS : Measurable (fun q : parabolicSubalgebra (R := 𝕂) B × lowerLie (E := 𝕂) B =>
      (q.1 : Matrix (Fin n) (Fin n) 𝕂) * (1 + (q.2 : Matrix (Fin n) (Fin n) 𝕂))) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))).measurable
  have hRHS : ((iwahoriConstant B μG μP νS νL U r •
        ((μP.restrict s).prod (νL.restrict RL)).map
          (fun q => (q.1 : GeneralLinear n 𝕂) * lowerUnit B q.2))).map Units.val =
      (μG U * (ν (closedBall 1 r))⁻¹) • ν.restrict (closedBall 1 r) := by
    rw [Measure.map_smul, Measure.map_map Units.continuous_val.measurable hmulL]
    have hfun : (Units.val ∘ fun q : B.parabolic 𝕂 × lowerLie (E := 𝕂) B =>
        (q.1 : GeneralLinear n 𝕂) * lowerUnit B q.2) =
        (fun q : Matrix (Fin n) (Fin n) 𝕂 × lowerLie (E := 𝕂) B =>
          q.1 * (1 + (q.2 : Matrix (Fin n) (Fin n) 𝕂))) ∘
          Prod.map (fun p : B.parabolic 𝕂 => (p : GeneralLinear n 𝕂).val) id := rfl
    rw [hfun, ← Measure.map_map hg (hmP.prodMap measurable_id),
      ← Measure.map_prod_map _ _ hmP measurable_id, Measure.map_id, hC, Measure.prod_smul_left,
      Measure.map_smul, smul_smul]
    have hfun' : (fun q : Matrix (Fin n) (Fin n) 𝕂 × lowerLie (E := 𝕂) B =>
        q.1 * (1 + (q.2 : Matrix (Fin n) (Fin n) 𝕂))) ∘
          Prod.map (Subtype.val : parabolicSubalgebra (R := 𝕂) B → Matrix (Fin n) (Fin n) 𝕂) id =
        fun q : parabolicSubalgebra (R := 𝕂) B × lowerLie (E := 𝕂) B =>
          (q.1 : Matrix (Fin n) (Fin n) 𝕂) * (1 + (q.2 : Matrix (Fin n) (Fin n) 𝕂)) := rfl
    rw [← Measure.map_id (μ := νL.restrict RL), Measure.map_prod_map _ _
      continuous_subtype_val.measurable measurable_id, Measure.map_map hg
      (continuous_subtype_val.measurable.prodMap measurable_id), hfun', hI]
    congr 1
    rw [iwahoriConstant]
    · exact ENNReal.div_mul_cancel hb0 hbtop
    all_goals first
      | exact hg.aemeasurable
      | exact Units.continuous_val.measurable.aemeasurable
  rw [← hRHS, hval.comap_map]

end Langlands.BaseChange.TwistedLocalDescent
