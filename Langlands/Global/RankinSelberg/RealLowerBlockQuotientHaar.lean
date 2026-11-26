import Langlands.Global.RankinSelberg.RealLastPivotChart
import Langlands.Global.RankinSelberg.RealLowerBlockMeasure
import Langlands.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure

/-! # The compatible real quotient Haar measure in lower-block coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Topology
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.RankinSelbergGlobal.RealLowerBlockQuotientHaar

open Langlands.GeneralLinear Langlands.QuotientIntegration Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure
  exists_pos_smul_eq_of_isMulRightInvariant)
open Langlands.RankinSelberg.GLDeterminantDensity (map_withDensity_comp)
open ArchimedeanLocal RealLastPivotChart RealLowerBlockMeasure
open ArchimedeanRealPairIdentity (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs
  sigmaFinite_rect sigmaFinite_haar)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
private local instance (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (lowerTriangularSubgroup n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (lowerTriangularSubgroup n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (lowerTriangularSubgroup n ℝ) :=
  IsEmbedding.subtypeVal.secondCountableTopology
private local instance (n : ℕ) : LocallyCompactSpace (lowerTriangularSubgroup n ℝ) :=
  (lowerTriangularSubgroup_isClosed n).locallyCompactSpace
private local instance (r : ℕ) : SecondCountableTopology (LeftUnipotentQuotient r ℝ) :=
  (leftQuotient_isOpenQuotientMap (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)).secondCountableTopology

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "T" => fun n => lowerTriangularSubgroup n ℝ
local notation "tri" => fun r => lowerTriangularQuotientMap (r + 1) ℝ

private theorem isOpenEmbedding_tri : ∀ r : ℕ, IsOpenEmbedding (tri r) := by
  intro r
  induction r with
  | zero =>
    have hAll : (T 1 : Set (G 1)) = univ := by
      ext g
      simp only [SetLike.mem_coe, mem_lowerTriangularSubgroup_iff, mem_univ, iff_true]
      intro i j hij
      exact ((Subsingleton.elim i j).not_lt hij).elim
    refine .of_continuous_injective_isOpenMap
      ((leftQuotient_isOpenQuotientMap (N 1)).continuous.comp continuous_subtype_val)
      lowerTriangularQuotientMap_injective ?_
    exact (leftQuotient_isOpenQuotientMap (N 1)).isOpenMap.comp
      ((hAll ▸ isOpen_univ : IsOpen (T 1 : Set (G 1))).isOpenEmbedding_subtypeVal.isOpenMap)
  | succ r ih =>
    let e := lowerTriangularBlockHomeomorph (r + 1) 1 ℝ
    have he : tri (r + 1) = lowerBlockQuotientChart ∘ Prod.map (tri r) id ∘ e.symm := by
      funext b
      rw [Function.comp_apply, Function.comp_apply]
      obtain ⟨⟨g, x, k⟩, rfl⟩ := e.surjective b
      rw [e.symm_apply_apply]
      rfl
    rw [he]
    exact isOpenEmbedding_realLastPivotChart.comp
      ((ih.prodMap IsOpenEmbedding.id).comp e.symm.isOpenEmbedding)

private theorem measure_compl_range_tri {r : ℕ} (D : RealQuotientMeasureData r) :
    D.measure (range (tri r))ᶜ = 0 := by
  let W := (range (tri r))ᶜ
  let q := leftQuotientMap (N (r + 1))
  have hW : MeasurableSet W := (isOpenEmbedding_tri r).isOpen_range.measurableSet.compl
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  have hR : ∀ S ∈ 𝓝 (0 : ℝ), ∃ t ∈ S, t ≠ 0 := by
    intro S hS
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hS
    refine ⟨ε / 2, hsub ?_, by positivity⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hZero : D.groupHaar (q ⁻¹' W) = 0 := by
    refine measure_mono_null ?_ (haar_setOf_not_upperUnipotent_mul_lowerTriangular hR D.groupHaar)
    intro g hg
    rintro ⟨u, hu, b, hb, rfl⟩
    apply hg
    have hq := leftQuotientMap_subgroup_mul (N (r + 1)) ⟨u, hu⟩ b
    exact ⟨⟨b, hb⟩, hq.symm⟩
  have hclosed : IsClosed (N (r + 1) : Set (G (r + 1))) := UpperUnipotent.isClosed
  obtain ⟨ρ, _, hρ, _⟩ := exists_continuous_isNormalizingFunction (N (r + 1)) hclosed D.unipotentHaar
  have hq : Measurable q := (leftQuotient_isOpenQuotientMap _).continuous.measurable
  change D.measure W = 0
  rw [D.compatible.eq_map_withDensity hclosed hρ, Measure.map_apply hq hW,
    withDensity_apply _ (hq hW)]
  exact setLIntegral_measure_zero _ _ hZero

private theorem triangularChart_right {r : ℕ} (b c : T (r + 1)) :
    tri r (b * c) = rightTranslate (N (r + 1)) c.val (tri r b) := rfl

private theorem pullTriangular_properties {r : ℕ} (D : RealQuotientMeasureData r) :
    let ρ := D.measure.comap (tri r)
    ρ.IsMulRightInvariant ∧ IsFiniteMeasureOnCompacts ρ ∧ ρ ≠ 0 ∧ ρ.map (tri r) = D.measure := by
  let ρ := D.measure.comap (tri r)
  let e := (isOpenEmbedding_tri r).measurableEmbedding
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  have hmap : ρ.map (tri r) = D.measure := by
    rw [e.map_comap, Measure.restrict_eq_self_of_ae_mem]
    exact measure_compl_range_tri D
  refine ⟨⟨fun b => ?_⟩, ⟨fun C hC => ?_⟩, ?_, hmap⟩
  · apply e.map_injective
    rw [Measure.map_map e.measurable (measurable_mul_const b)]
    have hcomp : tri r ∘ (fun c => c * b) = (rightTranslate (N (r + 1)) b.val) ∘ tri r :=
      funext fun c => triangularChart_right c b
    rw [hcomp, ← Measure.map_map (rightTranslate (N (r + 1)) b.val).continuous.measurable e.measurable,
      hmap, (D.compatible.right_invariant b.val).map_eq]
  · change D.measure.comap (tri r) C < ⊤
    rw [e.comap_apply D.measure C]
    exact (hC.image (isOpenEmbedding_tri r).continuous).measure_lt_top
  · intro hzero
    change ρ = 0 at hzero
    exact D.compatible.nonzero (by rw [← hmap, hzero, Measure.map_zero])

/-- A compatible real quotient measure is the lower-block product with
one trailing coordinate, up to a positive scalar. -/
def RealLowerBlockQuotientHaarStatement : Prop :=
  ∀ (r : ℕ) (D : RealQuotientMeasureData r) (E : RealQuotientMeasureData (r + 1))
    (ν : AdditiveHaarMeasure ℝ) (ρ : Measure (T 1))
    [SigmaFinite ρ] [IsFiniteMeasureOnCompacts ρ] [ρ.IsMulRightInvariant],
    ρ ≠ 0 → ∃ C : ℝ, 0 < C ∧
      E.measure = ENNReal.ofReal C •
        (lowerBlockProduct D ν ρ).map (lowerBlockQuotientChart (a := r + 1) (d := 1))

theorem realLowerBlockQuotientHaar : RealLowerBlockQuotientHaarStatement := by
  intro r D E ν ρ _ _ _ hρ
  obtain ⟨smallInv, smallFinite, smallNZ, smallPush⟩ := pullTriangular_properties D
  obtain ⟨largeInv, largeFinite, largeNZ, largePush⟩ := pullTriangular_properties E
  let small := D.measure.comap (tri r)
  let large := E.measure.comap (tri (r + 1))
  change small.IsMulRightInvariant at smallInv
  change IsFiniteMeasureOnCompacts small at smallFinite
  change small ≠ 0 at smallNZ
  change small.map (tri r) = D.measure at smallPush
  change large.IsMulRightInvariant at largeInv
  change IsFiniteMeasureOnCompacts large at largeFinite
  change large ≠ 0 at largeNZ
  change large.map (tri (r + 1)) = E.measure at largePush
  let := smallInv
  let := smallFinite
  let := largeInv
  let := largeFinite
  let := sigmaFinite_haar ν
  let := sigmaFinite_rect ν 1 (r + 1)
  let X := Matrix (Fin 1) (Fin (r + 1)) ℝ
  let A := T (r + 1) × X × T 1
  let e := lowerTriangularBlockHomeomorph (r + 1) 1 ℝ
  let β : A → LowerBlockQuotientParameters (r + 1) 1 ℝ := Prod.map (tri r) id
  have hβ : MeasurableEmbedding β :=
    ((isOpenEmbedding_tri r).prodMap IsOpenEmbedding.id).measurableEmbedding
  let dx := rectangularMeasure ν 1 (r + 1)
  let w (b : T (r + 1)) : ℝ≥0 := ((quotientDetAbs (tri r b)).toNNReal)⁻¹
  have hw : Continuous w := by
    apply Continuous.inv₀
    · exact continuous_real_toNNReal.comp
        (continuous_quotientDetAbs.comp (isOpenEmbedding_tri r).continuous)
    · intro b
      exact (Real.toNNReal_pos.mpr (quotientDetAbs_pos (tri r b))).ne'
  have hwne (b : T (r + 1)) : (w b : ℝ≥0∞) ≠ 0 := by
    apply ENNReal.coe_ne_zero.mpr
    exact inv_ne_zero (Real.toNNReal_pos.mpr (quotientDetAbs_pos (tri r b))).ne'
  let smallW := small.withDensity (fun b => (w b : ℝ≥0∞))
  let P := smallW.prod (dx.prod ρ)
  have hSmallPush : smallW.map (tri r) = D.measure.withDensity (lowerBlockDensity 1) := by
    have hEq : (fun b => (w b : ℝ≥0∞)) = lowerBlockDensity 1 ∘ tri r := by
      funext b
      simp [w, lowerBlockDensity]
    change (small.withDensity _).map _ = _
    rw [hEq]
    have h := map_withDensity_comp small (isOpenEmbedding_tri r).measurableEmbedding (lowerBlockDensity 1)
    exact h.trans (congrArg (fun μ => μ.withDensity (lowerBlockDensity 1)) smallPush)
  have hβP : P.map β = lowerBlockProduct D ν ρ := by
    change (smallW.prod (dx.prod ρ)).map (Prod.map (tri r) id) = _
    rw [← map_prod_map _ _ (isOpenEmbedding_tri r).continuous.measurable measurable_id,
      hSmallPush, Measure.map_id]
    rfl
  have heChart : tri (r + 1) ∘ e = lowerBlockQuotientChart ∘ β := by
    funext b
    rfl
  have hPush : (P.map e).map (tri (r + 1)) =
      (lowerBlockProduct D ν ρ).map lowerBlockQuotientChart := by
    rw [Measure.map_map (isOpenEmbedding_tri (r + 1)).continuous.measurable e.continuous.measurable,
      heChart, ← Measure.map_map isOpenEmbedding_realLastPivotChart.continuous.measurable hβ.measurable, hβP]
  have hPEinv : (P.map e).IsMulRightInvariant := by
    refine ⟨fun b => ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective b
    let R (z : A) : A := (z.1 * v.1, z.2.1 * v.1.val.val + z.2.2.val.val * v.2.1, z.2.2 * v.2.2)
    have hR : Measurable R := by
      refine (continuous_fst.mul continuous_const).measurable.prodMk ?_
      refine ((continuous_fst.comp continuous_snd).matrix_mul continuous_const).measurable.add
        (((Units.continuous_val.comp (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd))).matrix_mul continuous_const).measurable)
        |>.prodMk ((continuous_snd.comp continuous_snd).mul continuous_const).measurable
    have hβR : β ∘ R = lowerBlockRight v.1.val v.2.1 v.2.2 ∘ β := by
      funext z
      rfl
    have hAct := realLowerBlockProductInvariance r 1 D ν ρ v.1.val v.2.1 v.2.2
    have hRP : P.map R = P := by
      apply hβ.map_injective
      rw [Measure.map_map hβ.measurable hR, hβR, ← Measure.map_map hAct.measurable hβ.measurable,
        hβP, hAct.map_eq]
    have heR : (fun z => z * e v) ∘ e = e ∘ R := by
      funext z
      exact lowerTriangularBlockMap_mul z v
    rw [Measure.map_map (measurable_mul_const _) e.continuous.measurable, heR,
      ← Measure.map_map e.continuous.measurable hR, hRP]
  have hPEfin : IsFiniteMeasureOnCompacts (P.map e) := by
    let : IsLocallyFiniteMeasure smallW := IsLocallyFiniteMeasure.withDensity_coe hw
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply e.continuous.measurable hK.measurableSet]
    have hc := e.isCompact_preimage.mpr hK
    exact hc.measure_lt_top
  have hAnz : smallW ≠ 0 := by
    intro h0
    have hw0 := (withDensity_eq_zero_iff hw.measurable.coe_nnreal_ennreal.aemeasurable).mp h0
    exact smallNZ (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp (hw0.mono fun b hb => hwne b hb)))
  have hDxNZ : dx ≠ 0 := by
    intro h0
    have hpos := (isOpen_univ.measure_pos dx ⟨0, trivial⟩).ne'
    rw [h0] at hpos
    exact hpos rfl
  have hPNZ : P ≠ 0 := by
    intro h0
    have hh : P (univ ×ˢ (univ ×ˢ univ)) = 0 := by simp [h0]
    change (smallW.prod (dx.prod ρ)) (univ ×ˢ (univ ×ˢ univ)) = 0 at hh
    rw [Measure.prod_prod, Measure.prod_prod] at hh
    have ha : smallW univ ≠ 0 := fun h => hAnz (measure_univ_eq_zero.mp h)
    have hx : dx univ ≠ 0 := fun h => hDxNZ (measure_univ_eq_zero.mp h)
    have ht : ρ univ ≠ 0 := fun h => hρ (measure_univ_eq_zero.mp h)
    exact (mul_ne_zero ha (mul_ne_zero hx ht)) hh
  have hPENZ : P.map e ≠ 0 := fun h0 => hPNZ ((Measure.map_eq_zero_iff e.continuous.measurable.aemeasurable).mp h0)
  let := hPEinv
  let := hPEfin
  obtain ⟨C, hC, hScale⟩ := exists_pos_smul_eq_of_isMulRightInvariant large (P.map e) largeNZ hPENZ
  refine ⟨C, hC, ?_⟩
  rw [← largePush, hScale,
    Measure.map_smul _ (isOpenEmbedding_tri (r + 1)).continuous.measurable.aemeasurable, hPush]

end Langlands.Global.RankinSelbergGlobal.RealLowerBlockQuotientHaar
