import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalRankZeroFourierInjectivity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalDiscreteActionSeparation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalRankZero
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFullLeviSplitCenter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFullLeviFourierAction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RankZeroPacketStructure

/-! # Proof of local Fourier injectivity in relative semisimple rank zero -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
open Langlands.Aubert.General Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

private theorem exists_centralHeight_lintegral_lt_top
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [T2Space Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ]
    [MeasurableSpace Γ] [BorelSpace Γ]
    {A : Subgroup Γ} (hA : IsClosed (A : Set Γ))
    [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
    {muA : Measure A} [SFinite muA] [muA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts muA]
    {muG : Measure Γ} [IsFiniteMeasureOnCompacts muG] {muQ : Measure (LeftQuotient A)}
    (hQ : IsCompatible A muG muA muQ) {Ξ σ : Γ → ℝ}
    (hΞ : ∀ g, 0 < Ξ g) (hΞc : Continuous Ξ) (hσc : Continuous σ)
    (hΞA : ∀ (a : A) g, Ξ ((a : Γ) * g) = Ξ g)
    (hσ : ∀ g, 0 ≤ σ g) (hσmul : ∀ g h, σ (g * h) ≤ σ g + σ h)
    (hw : SquareIntegrableWeight muG Ξ σ) :
    ∃ d₀ : ℝ, ∫⁻ a : A, ENNReal.ofReal ((1 + σ a) ^ (-d₀)) ∂muA < ⊤ := by
  obtain ⟨d, hd⟩ := hw
  let w : Γ → ℝ≥0∞ := fun g => ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ)))
  have hwmeas : Measurable w := ENNReal.measurable_ofReal.comp
    ((hΞc.pow 2).mul ((continuous_const.add hσc).rpow_const fun g => Or.inl (by
      change 1 + σ g ≠ 0
      linarith [hσ g]))).measurable
  have hWeil := lintegral_lintegral_out_eq hA hQ hwmeas
  have hfinite : ∫⁻ q, ∫⁻ a : A, w ((a : Γ) * q.out) ∂muA ∂muQ < ⊤ := hWeil.trans_lt hd
  have hq : ∃ q : LeftQuotient A, ∫⁻ a : A, w ((a : Γ) * q.out) ∂muA < ⊤ := by
    by_contra! h
    have htop (q : LeftQuotient A) :
        ∫⁻ a : A, w ((a : Γ) * q.out) ∂muA = ⊤ := top_unique (h q)
    have hmass : muQ Set.univ ≠ 0 := fun hz => hQ.nonzero (Measure.measure_univ_eq_zero.mp hz)
    simp only [htop, lintegral_const, ENNReal.top_mul hmass, lt_self_iff_false] at hfinite
  obtain ⟨q, hq⟩ := hq
  let g := q.out
  let c : ℝ := Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))
  have hc : 0 < c := mul_pos (sq_pos_of_pos (hΞ g))
    (Real.rpow_pos_of_pos (by linarith [hσ g]) _)
  have hle (a : A) : ENNReal.ofReal c * ENNReal.ofReal ((1 + σ a) ^ (-(d : ℝ))) ≤
      w ((a : Γ) * g) := by
    have hadd : 1 + σ ((a : Γ) * g) ≤ (1 + σ a) * (1 + σ g) := by
      nlinarith [hσmul (a : Γ) g, mul_nonneg (hσ a) (hσ g)]
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith [hσ ((a : Γ) * g)]) hadd
      (neg_nonpos.mpr (Nat.cast_nonneg d) : -(d : ℝ) ≤ 0)
    rw [Real.mul_rpow (by linarith [hσ a]) (by linarith [hσ g])] at hp
    rw [← ENNReal.ofReal_mul hc.le]
    apply ENNReal.ofReal_le_ofReal
    rw [hΞA, show c * (1 + σ a) ^ (-(d : ℝ)) =
      Ξ g ^ 2 * ((1 + σ a) ^ (-(d : ℝ)) * (1 + σ g) ^ (-(d : ℝ))) by unfold c; ring]
    exact mul_le_mul_of_nonneg_left hp (sq_nonneg _)
  have hfin := (lintegral_mono hle).trans_lt hq
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hfin
  refine ⟨d, ?_⟩
  by_contra! h
  rw [top_unique h, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hc)] at hfin
  exact lt_irrefl _ hfin

open RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2500000 in
/-- At rank zero, the full-Levi Fourier transform separates Schwartz functions
by split-center Fourier uniqueness and the finite projected cuspidal levels. -/
theorem rationalRankZeroFourierInjectivity :
    RationalRankZeroFourierInjectivityStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi hzero hG' S' j hj ν hν K hKc hPK N _ ρ muG _ _
    hw T a ha _ _ _ mu _ _ d hdelta hT f hf
  let := hG.isAffineHom
  have hzero' : relativeRootRank j = 0 :=
    (relativeRootRank_eq_of_maximalSplitTori hG i j hi hj).symm.trans hzero
  have hsimple := simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty j ν
    (RankZero.relativeRoots_eq_empty_of_rankZero hG hj hzero')
  have hcentral := (rankZero_isCentral_unipotent_eq_bot hG hj hν hsimple).1
  have hs : IsSplitComponent j := ⟨⟨hj.1, hcentral⟩, fun S'' j' hj' => hj.2 S'' j' hj'.1⟩
  let A := (rationalPoints.map j).range
  have hA : A ≤ Subgroup.center (rationalPoints G) := hcentral.range_le_center
  have hAc : IsClosed (A : Set (rationalPoints G)) := isClosed_range_splitComponent G j hs
  let : A.Normal := A.normal_of_le_center hA
  let : LocallyCompactSpace A := hAc.locallyCompactSpace
  let : SecondCountableTopology A := inferInstanceAs
    (SecondCountableTopology (A : Set (rationalPoints G)))
  let : BorelSpace A := Subtype.borelSpace _
  let : IsClosed (A : Set (rationalPoints G)) := hAc
  let : MeasurableSpace (LeftQuotient A) := borel _
  let : BorelSpace (LeftQuotient A) := ⟨rfl⟩
  let : MeasurableSpace (rationalPoints G ⧸ A) := borel _
  let : BorelSpace (rationalPoints G ⧸ A) := ⟨rfl⟩
  let muA : Measure A := Measure.haar
  let muQ : Measure (rationalPoints G ⧸ A) := Measure.haar
  let : muA.IsMulRightInvariant := isMulRightInvariant_of_le_center hA muA
  obtain ⟨muW, hW⟩ := compatibleMeasureExists A hAc muG muA
  have hH := exists_centralHeight_lintegral_lt_top hAc hW (rationalXi_pos K.isOpen hKc hPK)
    (continuous_rationalXi K.isOpen hKc hPK) (continuous_rationalHeight (F := F) ρ)
    (fun a g => rationalXi_mul_of_mem_range K.isOpen hKc hPK hcentral a.2 g)
    (rationalHeight_nonneg ρ) (rationalHeight_mul_le ρ) hw
  have hcent := rationalCentralWeights K.isOpen hKc hPK hcentral ρ muA hH
  let : Fintype (RationalPointFamily.SimpleRoot j ν) :=
    (hj.isSplitSubtorus.1.finite_simpleRelativeRoots j ν).fintype
  let p := standardIndex hG' hj hν Finset.univ
  have hP : parabolic p = ⊤ :=
    RationalPointFamily.parabolic_univ_eq_top j ν standardCocharacter hG' hj hν
  have hM : levi p = ⊤ :=
    RationalPointFamily.levi_univ_eq_top j ν standardCocharacter hG' hj hν
  have hU : radical p = ⊥ := RationalPointFamily.unipotent_univ_eq_bot j ν
  have hmap :=
    fullLeviSplitCenter_map hG' hj hν (chosenLeviModel p) (a p) j (ha p) hs hM
  refine rationalCuspidalDiscreteActionSeparationOfWeights.{u, uV} F G hG' S' j hj ν hν K hKc
    hPK N ρ S' j hs muA muG muQ hcent (rationalL2Weights K.isOpen hKc hPK ρ hw)
    (fun χ H _ => finiteDimensional_rationalCuspidalCentralLevelSpan_of_simpleRoots_empty
      hG' hj hν hsimple hKc hPK ρ hs muA (χ : A →ₜ* ℂˣ).toMonoidHom H)
    f ?_ ?_
  · rw [rationalCuspidalSubmodule_eq_top_of_simpleRoots_empty hKc hPK ρ hsimple]
    exact Submodule.mem_top
  · let C := (chosenLeviModel p).splitCenter (a p)
    let hC := (chosenLeviModel p).splitCenter_le_center (a p) (ha p)
    apply rationalFullLeviFourierActionVanishing hG' hj hν hKc hPK ρ hw p (d p) (hdelta p)
      A hA muQ C hC (mu p) (hT p) hP hM hU hmap f
    intro B hB
    let O : OrbitClass (chosenLeviModel p) (a p) (ha p) (mu p) :=
      Quotient.mk _ (discreteSeriesClass C hC (mu p) B hB)
    let B' := orbitRepresentativeMember (chosenLeviModel p) (a p) (ha p) (mu p) O B hB rfl
    let t : RationalSemistandardTheta.{u, uV} a ha mu := ⟨p, O⟩
    have ht := congrArg (fun w : RationalSemistandardThetaSections.{u, uV} a ha mu => w t B') hf
    exact ht

end Langlands.HarishChandraSchwartz
