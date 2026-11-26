import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralUniformizerCellVolumeStatement
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Langlands.Representation.Hecke.DoubleCoset
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge

/-! # Proof of the central uniformizer quotient cell-volume identity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.HarishChandraSchwartz

open GroupScheme Plancherel QuotientIntegration Langlands.AlgebraicGeometry.PointTopology

private theorem measure_image_eq_of_counting_of_injOn
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (C : Subgroup Γ)
    [MeasurableSpace C] [BorelSpace C] [MeasurableMul C]
    [MeasurableSpace (LeftQuotient C)] [BorelSpace (LeftQuotient C)]
    (μΓ : Measure Γ) [μΓ.IsHaarMeasure] (μQ : Measure (LeftQuotient C))
    (hcompat : IsCompatible C μΓ Measure.count μQ)
    {D : Set Γ} (hDc : IsCompact D) (hDo : IsOpen D)
    (hinj : Set.InjOn (leftQuotientMap C) D) :
    μQ (leftQuotientMap C '' D) = μΓ D := by
  classical
  let E := leftQuotientMap C '' D
  let f : Γ → ℂ := D.indicator (fun _ => 1)
  have hDcl : IsClopen D := ⟨hDc.isClosed, hDo⟩
  have hfc : Continuous f := hDcl.continuous_indicator continuous_const
  have hfs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact hDc Set.support_indicator_subset
  have hEo : IsOpen E := (leftQuotient_isOpenQuotientMap C).isOpenMap _ hDo
  have hEc : IsCompact E := hDc.image (leftQuotient_isOpenQuotientMap C).continuous
  have havg : quotientAverage C Measure.count f = E.indicator (fun _ => (1 : ℂ)) := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      let S : Set C := {c | (c : Γ) * x ∈ D}
      have hf : (fun c : C => f ((c : Γ) * x)) = S.indicator (fun _ => (1 : ℂ)) := by
        funext c
        simp only [f, Set.indicator_apply, S, Set.mem_ofPred_eq]
      rw [quotientAverage_mk, hf]
      change (∫ c, S.indicator (fun _ => (1 : ℂ)) c ∂Measure.count) =
        E.indicator (fun _ => (1 : ℂ)) (leftQuotientMap C x)
      by_cases hx : leftQuotientMap C x ∈ E
      · obtain ⟨y, hy, hq⟩ := hx
        let c : C := ⟨y * x⁻¹, QuotientGroup.rightRel_apply.mp (Quotient.exact hq.symm)⟩
        have hc : c ∈ S := by
          change (y * x⁻¹) * x ∈ D
          rwa [inv_mul_cancel_right]
        have hS : S = {c} := by
          ext b
          constructor
          · intro hb
            apply Set.mem_singleton_iff.mpr
            apply Subtype.ext
            exact mul_right_cancel (hinj hb hc (by simp only [leftQuotientMap_subgroup_mul]))
          · intro hb
            rw [Set.mem_singleton_iff.mp hb]
            exact hc
        have hx' : leftQuotientMap C x ∈ E := ⟨y, hy, hq⟩
        rw [hS, integral_indicator_const _ (measurableSet_singleton c),
          measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
          Set.indicator_of_mem hx']
      · have hS : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun c hc =>
          hx ⟨(c : Γ) * x, hc, leftQuotientMap_subgroup_mul C c x⟩
        rw [hS, Set.indicator_empty, integral_zero, Set.indicator_of_notMem hx]
  have heq := hcompat.integral_formula f hfc hfs
  change _ = ∫ x, D.indicator (fun _ => (1 : ℂ)) x ∂μΓ at heq
  rw [havg, integral_indicator_const _ hEo.measurableSet,
    integral_indicator_const _ hDo.measurableSet] at heq
  let : μQ.Regular := hcompat.regular
  apply (ENNReal.toReal_eq_toReal_iff' hEc.measure_lt_top.ne hDc.measure_lt_top.ne).mp
  simpa only [Complex.real_smul, mul_one, Complex.ofReal_re, measureReal_def] using
    congrArg Complex.re heq

/-- The rational double coset has one representative in each quotient fiber
that it meets, so its quotient mass is its ambient mass. -/
theorem centralUniformizerCellVolume : CentralUniformizerCellVolumeStatement.{u} := by
  intro F _ _ _ _ G hG A a ha
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  have : T2Space F := BruhatTits.localField_t2Space F
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let C := RenardCartan.C0 A a
  let H := rationalCharacterValuation G
  dsimp only
  intro K hK g
  let D := DoubleCoset.doubleCoset g K K
  have hK1 {k : rationalPoints G} (hk : k ∈ K) : H k = 1 := by
    change k ∈ (rationalCharacterValuation G).ker
    rw [rationalCharacterValuation_ker]
    exact compactSubgroup_le_rationalCommonNormKernel G K.toSubgroup hK hk
  have hDVal {x : rationalPoints G} (hx : x ∈ D) : H x = H g := by
    obtain ⟨k, hk, l, hl, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    rw [map_mul, map_mul, hK1 hk, hK1 hl, one_mul, mul_one]
  have hCVal : Set.InjOn H (C : Set (rationalPoints G)) := by
    intro x hx y hy hxy
    exact (RenardCartan.bijOn_C0_splitValuationImage a ha.isCentralSplitTorus.isSplitSubtorus.1
      (ha.finiteIndex_range_characterRestrict hG)).2.1 hx hy (Subtype.ext hxy)
  have hDinj : Set.InjOn (leftQuotientMap C) D := by
    intro x hx y hy hxy
    have hyx : y * x⁻¹ ∈ C := QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)
    have hval : H (y * x⁻¹) = H 1 := by
      rw [map_mul, map_inv, hDVal hy, hDVal hx, mul_inv_cancel, map_one]
    exact (mul_inv_eq_one.mp (hCVal hyx C.one_mem hval)).symm
  refine ⟨hDinj, ?_⟩
  intro _ _ _ _ _ _ μG _ μQ hcompat
  exact measure_image_eq_of_counting_of_injOn C μG μQ hcompat
    (Hecke.TestFunction.isCompact_doubleCosetSet K hK g)
    (Hecke.TestFunction.isOpen_doubleCosetSet K g) hDinj

end Langlands.HarishChandraSchwartz
