import Langlands.Group.GL.LowerTriangularBlockCoordinates
import Langlands.Group.GL.LowerTriangularBigCellConull
import Langlands.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure
import Langlands.Representation.RankinSelberg.LowerBlockWeightedProductInvariance

/-!
# Lower-block comparison of quotient measures

A compatible quotient measure on `N_m \ GL_m` is the pushforward, along the open
cell `B⁻_m → N_m \ GL_m`, of its pullback to `B⁻_m`, which is right invariant and
finite on compacts. In block coordinates `B⁻_a × M_{d×a} × B⁻_d ≃ B⁻_{a+d}` the
determinant-weighted product of the pulled-back measure on `B⁻_a`, an additive
Haar measure on `M_{d×a}` and a right-invariant measure on `B⁻_d` is right
invariant on `B⁻_{a+d}`. Uniqueness of right-invariant measures then makes every
compatible quotient measure on `N_{a+d} \ GL_{a+d}` a positive multiple of the
lower-block chart pushforward of `D μ_a × dx × ρ`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Measure Topology Set GeneralLinear QuotientIntegration HarmonicAnalysis
open scoped ENNReal NNReal

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

set_option linter.overlappingInstances false in
/-- The pullback of a compatible quotient measure on `N_m \ GL_m` along the open
cell `B⁻_m → N_m \ GL_m` is right invariant, finite on compacts, σ-finite and
nonzero, and its pushforward along the cell is the quotient measure. -/
theorem lowerTriangularQuotientMap_comap_of_isCompatible (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (GeneralLinear m F.Carrier)
    letI : BorelSpace (GeneralLinear m F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent m F.Carrier)
    letI : BorelSpace (upperUnipotent m F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent m F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent m F.Carrier)) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup m F.Carrier)
    ∀ (μG : Measure (GeneralLinear m F.Carrier)) (μH : Measure (upperUnipotent m F.Carrier))
      [μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular]
      [μH.IsMulRightInvariant] (μ : Measure (LeftQuotient (upperUnipotent m F.Carrier))),
      IsCompatible (upperUnipotent m F.Carrier) μG μH μ →
      let ρ := μ.comap (lowerTriangularQuotientMap m F.Carrier)
      ρ.IsMulRightInvariant ∧ IsFiniteMeasureOnCompacts ρ ∧ SigmaFinite ρ ∧ ρ ≠ 0 ∧
        ρ.map (lowerTriangularQuotientMap m F.Carrier) = μ := by
  intro μG μH _ _ _ _ _ μ hμ ρ
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let mG : MeasurableSpace (GeneralLinear m F.Carrier) := borel _
  have : BorelSpace (GeneralLinear m F.Carrier) := ⟨rfl⟩
  let mN : MeasurableSpace (upperUnipotent m F.Carrier) := borel _
  have : BorelSpace (upperUnipotent m F.Carrier) := ⟨rfl⟩
  let mQ : MeasurableSpace (LeftQuotient (upperUnipotent m F.Carrier)) := borel _
  have : BorelSpace (LeftQuotient (upperUnipotent m F.Carrier)) := ⟨rfl⟩
  let mB : MeasurableSpace (lowerTriangularSubgroup m F.Carrier) := borel _
  have : BorelSpace (lowerTriangularSubgroup m F.Carrier) := ⟨rfl⟩
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup m
  have := T.generalLinearLocallyCompactSpace m
  have := T.generalLinearSecondCountableTopology m
  have : SecondCountableTopology (lowerTriangularSubgroup m F.Carrier) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (lowerTriangularSubgroup m F.Carrier) :=
    (lowerTriangularSubgroup_isClosed m).locallyCompactSpace
  have := hμ.regular
  obtain ⟨hinv, hfin, hmap⟩ :=
    comap_lowerTriangularQuotientMap_properties T m μ inferInstance hμ.right_invariant
  have hcompl : (range (lowerTriangularQuotientMap m F.Carrier))ᶜ =
      {q | ∀ b ∈ lowerTriangularSubgroup m F.Carrier,
        (Quotient.mk _ b : LeftQuotient (upperUnipotent m F.Carrier)) ≠ q} := by
    ext q
    simp only [mem_compl_iff, mem_range, not_exists, lowerTriangularQuotientMap_apply,
      Subtype.forall, mem_ofPred_eq]
  have hm : ρ.map (lowerTriangularQuotientMap m F.Carrier) = μ :=
    hmap (hcompl ▸ padic_lowerTriangular_leftQuotient_conull T m μG μH μ hμ)
  have : IsFiniteMeasureOnCompacts ρ := hfin
  refine ⟨hinv, hfin, inferInstance, ?_, hm⟩
  intro h0
  exact hμ.nonzero (by rw [← hm, h0, Measure.map_zero])

set_option linter.overlappingInstances false in
/-- Lower-block comparison of quotient measures. Let `μa` and `μad` be compatible
quotient measures on `N_a \ GL_a` and `N_{a+d} \ GL_{a+d}`, `η` an additive Haar
measure on `F` and `ρ` a nonzero right-invariant measure on `B⁻_d`, σ-finite and
finite on compacts. Then `μad = C • map chart ((μa.withDensity D).prod (dx.prod ρ))`
for some real `C > 0`, where `chart ([g], x, h) = [[[g,0],[x,h]]]`,
`D [g] = |det g|^(-d)` and `dx` is the rectangular Haar measure built from `η`. -/
theorem lowerBlockQuotient_eq_smul_map_chart (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (GeneralLinear a F.Carrier)
    letI : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent a F.Carrier)
    letI : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent a F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent a F.Carrier)) := ⟨rfl⟩
    letI := borel (GeneralLinear (a + d) F.Carrier)
    letI : BorelSpace (GeneralLinear (a + d) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (a + d) F.Carrier)
    letI : BorelSpace (upperUnipotent (a + d) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (a + d) F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent (a + d) F.Carrier)) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup d F.Carrier)
    letI : BorelSpace (lowerTriangularSubgroup d F.Carrier) := ⟨rfl⟩
    ∀ (η : AdditiveHaarMeasure F.Carrier)
      (μGa : Measure (GeneralLinear a F.Carrier)) (μHa : Measure (upperUnipotent a F.Carrier))
      [μGa.IsHaarMeasure] [μGa.Regular] [μHa.IsHaarMeasure] [μHa.Regular]
      [μHa.IsMulRightInvariant]
      (μGad : Measure (GeneralLinear (a + d) F.Carrier))
      (μHad : Measure (upperUnipotent (a + d) F.Carrier))
      [μGad.IsHaarMeasure] [μGad.Regular] [μHad.IsHaarMeasure] [μHad.Regular]
      [μHad.IsMulRightInvariant]
      (μa : Measure (LeftQuotient (upperUnipotent a F.Carrier)))
      (μad : Measure (LeftQuotient (upperUnipotent (a + d) F.Carrier))),
      IsCompatible (upperUnipotent a F.Carrier) μGa μHa μa →
      IsCompatible (upperUnipotent (a + d) F.Carrier) μGad μHad μad →
      ∀ (ρ : Measure (lowerTriangularSubgroup d F.Carrier)) [SigmaFinite ρ]
        [IsFiniteMeasureOnCompacts ρ] [ρ.IsMulRightInvariant], ρ ≠ 0 →
      ∃ C : ℝ, 0 < C ∧
        μad = ENNReal.ofReal C • Measure.map (lowerBlockQuotientChart (a := a) (d := d))
          ((μa.withDensity (lowerBlockQuotientDensity T a d)).prod
            ((rectangularMeasure η d a).prod ρ)) := by
  intro η μGa μHa _ _ _ _ _ μGad μHad _ _ _ _ _ μa μad hμa hμad ρ _ _ _ hρ
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (GeneralLinear a F.Carrier)
  have : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent a F.Carrier)
  have : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent a F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent a F.Carrier)) := ⟨rfl⟩
  let := borel (GeneralLinear (a + d) F.Carrier)
  have : BorelSpace (GeneralLinear (a + d) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (a + d) F.Carrier)
  have : BorelSpace (upperUnipotent (a + d) F.Carrier) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent (a + d) F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent (a + d) F.Carrier)) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup d F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup d F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup a F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup a F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup (a + d) F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup (a + d) F.Carrier) := ⟨rfl⟩
  have := T.generalLinearTopologicalGroup a
  have := T.generalLinearTopologicalGroup d
  have := T.generalLinearTopologicalGroup (a + d)
  have := T.generalLinearLocallyCompactSpace a
  have := T.generalLinearLocallyCompactSpace d
  have := T.generalLinearLocallyCompactSpace (a + d)
  have := T.generalLinearSecondCountableTopology a
  have := T.generalLinearSecondCountableTopology d
  have := T.generalLinearSecondCountableTopology (a + d)
  have : SecondCountableTopology (lowerTriangularSubgroup a F.Carrier) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (lowerTriangularSubgroup d F.Carrier) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (lowerTriangularSubgroup (a + d) F.Carrier) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (lowerTriangularSubgroup a F.Carrier) :=
    (lowerTriangularSubgroup_isClosed a).locallyCompactSpace
  have : LocallyCompactSpace (lowerTriangularSubgroup (a + d) F.Carrier) :=
    (lowerTriangularSubgroup_isClosed (a + d)).locallyCompactSpace
  have : SecondCountableTopology (LeftQuotient (upperUnipotent a F.Carrier)) :=
    (leftQuotient_isOpenQuotientMap _).secondCountableTopology
  -- Pull both quotient measures back to the lower triangular groups.
  obtain ⟨hρa_inv, hρa_fin, hρa_sf, hρa_ne, hρa_map⟩ :=
    lowerTriangularQuotientMap_comap_of_isCompatible T a μGa μHa μa hμa
  obtain ⟨hρad_inv, hρad_fin, -, hρad_ne, hρad_map⟩ :=
    lowerTriangularQuotientMap_comap_of_isCompatible T (a + d) μGad μHad μad hμad
  set ρa := μa.comap (lowerTriangularQuotientMap a F.Carrier) with hρa_def
  set ρad := μad.comap (lowerTriangularQuotientMap (a + d) F.Carrier) with hρad_def
  set w := lowerTriangularBlockDensity T a d with hw_def
  set dx := rectangularMeasure η d a with hdx_def
  set θ := lowerTriangularBlockMap a d F.Carrier with hθ_def
  have hβa : Measurable (lowerTriangularQuotientMap a F.Carrier) :=
    (lowerTriangularQuotientMap_measurableEmbedding T a).measurable
  have hβad : Measurable (lowerTriangularQuotientMap (a + d) F.Carrier) :=
    (lowerTriangularQuotientMap_measurableEmbedding T (a + d)).measurable
  have hθm : Measurable θ := continuous_lowerTriangularBlockMap.measurable
  have hchart : Measurable (lowerBlockQuotientChart (a := a) (d := d) (R := F.Carrier)) :=
    continuous_lowerBlockQuotientChart.measurable
  have hw : Continuous w := continuous_lowerTriangularBlockDensity T a d
  have hwtop : ∀ b, w b ≠ ∞ := by
    intro b
    rw [hw_def, lowerTriangularBlockDensity_eq_coe]
    exact ENNReal.coe_ne_top
  have hw0 : ∀ b, w b ≠ 0 := by
    intro b
    rw [hw_def, lowerTriangularBlockDensity_eq_coe]
    exact ENNReal.coe_ne_zero.mpr (zpow_ne_zero _ (T.determinantNorm a b.val).ne_zero)
  -- The weighted measure on `B⁻_a` pushes forward to the weighted quotient measure.
  have hdens : μa.withDensity (lowerBlockQuotientDensity T a d) =
      (ρa.withDensity w).map (lowerTriangularQuotientMap a F.Carrier) := by
    rw [← hρa_map]
    ext s hs
    rw [withDensity_apply _ hs, Measure.map_apply hβa hs, withDensity_apply _ (hβa hs),
      setLIntegral_map hs (measurable_lowerBlockQuotientDensity T a d) hβa]
    rfl
  set P := (ρa.withDensity w).prod (dx.prod ρ) with hP_def
  have hcomp : lowerBlockQuotientChart ∘ Prod.map (lowerTriangularQuotientMap a F.Carrier) id =
      lowerTriangularQuotientMap (a + d) F.Carrier ∘ θ := by
    funext z
    rfl
  have hmapchart : Measure.map (lowerBlockQuotientChart (a := a) (d := d))
      ((μa.withDensity (lowerBlockQuotientDensity T a d)).prod (dx.prod ρ)) =
      (P.map θ).map (lowerTriangularQuotientMap (a + d) F.Carrier) := by
    rw [hdens, ← Measure.map_id (μ := dx.prod ρ), map_prod_map _ _ hβa measurable_id,
      Measure.map_map hchart (hβa.prodMap measurable_id), hcomp,
      ← Measure.map_map hβad hθm]
  -- The block-coordinate image of the weighted product is right invariant.
  have hνinv : (P.map θ).IsMulRightInvariant := by
    refine ⟨fun c => ?_⟩
    obtain ⟨v, rfl⟩ := (lowerTriangularBlockEquiv a d F.Carrier).surjective c
    have hφ := measurePreserving_lowerBlockWeightedProduct_mulRight T a d η ρa ρ
      v.1 v.2.1 v.2.2
    rw [Measure.map_map (measurable_mul_const _) hθm]
    have hfun : (fun k => k * lowerTriangularBlockEquiv a d F.Carrier v) ∘ θ =
        θ ∘ (fun z : lowerTriangularSubgroup a F.Carrier ×
            Matrix (Fin d) (Fin a) F.Carrier × lowerTriangularSubgroup d F.Carrier =>
          (z.1 * v.1, z.2.1 * v.1.val.val + z.2.2.val.val * v.2.1, z.2.2 * v.2.2)) := by
      funext z
      exact lowerTriangularBlockMap_mul z v
    rw [hfun, ← Measure.map_map hθm hφ.measurable, hφ.map_eq]
  -- It is finite on compacts.
  have hAloc : IsLocallyFiniteMeasure (ρa.withDensity w) := by
    have hA : ρa.withDensity w = ρa.withDensity fun b => ((w b).toNNReal : ℝ≥0∞) :=
      congrArg _ (funext fun b => (ENNReal.coe_toNNReal (hwtop b)).symm)
    rw [hA]
    exact IsLocallyFiniteMeasure.withDensity_coe
      (ENNReal.continuousOn_toNNReal.comp_continuous hw hwtop)
  have hνfin : IsFiniteMeasureOnCompacts (P.map θ) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hθm hK.measurableSet]
    exact ((lowerTriangularBlockHomeomorph a d F.Carrier).isCompact_preimage.mpr hK).measure_lt_top
  -- It is nonzero.
  have hAne : ρa.withDensity w ≠ 0 := by
    intro h0
    rw [withDensity_eq_zero_iff hw.measurable.aemeasurable] at h0
    exact hρa_ne (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp
      (h0.mono fun b hb => hw0 b hb)))
  have hdxne : dx ≠ 0 := by
    intro h0
    have := (isOpen_univ.measure_pos dx ⟨0, trivial⟩).ne'
    rw [h0] at this
    exact this rfl
  have hPne : P ≠ 0 := by
    intro h0
    have h := congrArg (fun ν : Measure _ => ν (univ ×ˢ (univ ×ˢ univ))) h0
    simp only [hP_def, Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      Measure.measure_univ_eq_zero] at h
    rcases h with h | h | h
    exacts [hAne h, hdxne h, hρ h]
  have hνne : P.map θ ≠ 0 := fun h0 => hPne ((Measure.map_eq_zero_iff hθm.aemeasurable).mp h0)
  -- Uniqueness of right-invariant measures on `B⁻_{a+d}`.
  obtain ⟨C, hC, hCeq⟩ := exists_pos_smul_eq_of_isMulRightInvariant ρad (P.map θ) hρad_ne hνne
  refine ⟨C, hC, ?_⟩
  rw [hmapchart, ← Measure.map_smul, ← hCeq, hρad_map]
  exact hβad.aemeasurable

end Langlands.RankinSelberg
