import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientCoordinates
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement
import Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof
import Langlands.Analysis.Local.QuotientPositiveLifting
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration

open MeasureTheory Measure ProbabilityTheory GeneralLinear QuotientIntegration TwoBlockJacquet
  TwoBlockDeformation TwoBlockUnipotentQuotient
open scoped ENNReal NNReal CompactlySupported

universe uF

section Tower

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] [SecondCountableTopology F]

private instance matrix_locallyCompact (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → F))

private instance matrix_secondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))

private instance gl_secondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear n F) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private instance unipotent_secondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear.upperUnipotent n F) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (GeneralLinear.upperUnipotent n F : Set (GeneralLinear n F))

private instance unipotent_locallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear.upperUnipotent n F) :=
  UpperUnipotent.locallyCompactSpace

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

private instance block_secondCountable :
    SecondCountableTopology (blockUnipotent h F) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (blockUnipotent h F : Set (GeneralLinear (t + 1) F))

private instance block_locallyCompact : LocallyCompactSpace (blockUnipotent h F) :=
  (isClosed_blockUnipotent h F).isClosedEmbedding_subtypeVal.locallyCompactSpace

private instance blockQuotient_t2 : T2Space (BlockQuotient h F) :=
  leftQuotient_t2Space _ (isClosed_blockUnipotent h F)

private instance blockQuotient_locallyCompact : LocallyCompactSpace (BlockQuotient h F) :=
  leftQuotient_locallyCompactSpace _

private instance blockQuotient_secondCountable :
    SecondCountableTopology (BlockQuotient h F) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (blockUnipotent h F))

private instance unipotentQuotient_locallyCompact :
    LocallyCompactSpace (LeftUnipotentQuotient t F) :=
  leftQuotient_locallyCompactSpace _

private instance unipotentQuotient_secondCountable :
    SecondCountableTopology (LeftUnipotentQuotient t F) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (GeneralLinear.upperUnipotent (t + 1) F))

local notation "O" => Valuation.integer (ValuativeRel.valuation F)

omit [T2Space F] [SecondCountableTopology F] in
theorem continuous_fiberPoint_left (g : GeneralLinear (t + 1) F) :
    Continuous fun x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F => fiberPoint h F x g :=
  continuous_quotient_mk'.comp ((continuous_upperRadical h F).mul continuous_const)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [T2Space F] [SecondCountableTopology F] in
theorem continuous_projection' : Continuous (projection h F) :=
  Continuous.quotient_lift continuous_quotient_mk' _

variable [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (GeneralLinear (t + 1) F)] [BorelSpace (GeneralLinear (t + 1) F)]
  [MeasurableSpace (blockUnipotent h F)] [BorelSpace (blockUnipotent h F)]
  [MeasurableSpace (upperUnipotent (t + 1) F)] [BorelSpace (upperUnipotent (t + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient t F)] [BorelSpace (LeftUnipotentQuotient t F)]
  [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)]

omit [MeasurableSpace (GeneralLinear (t + 1) F)] [BorelSpace (GeneralLinear (t + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient t F)] [BorelSpace (LeftUnipotentQuotient t F)]
  [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)] in
/-- **Fiber unfolding.** For a nonnegative compactly supported continuous `f` on
`GL_(t+1)`, integrating the `H`-average of `f` over the radical fiber `x ↦ [u(x) g]_H`
gives `c` times the `N`-average of `f` at `[g]_N`, where `c` is the `μR`-mass of the
integral rectangle. -/
theorem lintegral_fiberPoint_quotientAverageReal
    (μH : Measure (blockUnipotent h F)) [μH.IsHaarMeasure] [IsMulRightInvariant μH]
    (hμH : μH {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} = 1)
    [IsMulRightInvariant (unipotentHaar F t)]
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μR.IsAddHaarMeasure]
    (f : GeneralLinear (t + 1) F → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hf0 : ∀ y, 0 ≤ f y) (g : GeneralLinear (t + 1) F) :
    ∫⁻ x, ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f (fiberPoint h F x g))
        ∂μR =
      μR {x | ∀ a c, x a c ∈ O} *
        ENNReal.ofReal (quotientAverageReal (upperUnipotent (t + 1) F) (unipotentHaar F t) f
          (Quotient.mk _ g)) := by
  have hH := isClosed_blockUnipotent h F
  have hint : ∀ x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F,
      Integrable (fun b : blockUnipotent h F => f (b.val * (upperRadical h F x * g))) μH :=
    fun x => integrable_subgroup_mul_of_hasCompactSupport _ hH μH f hfc hfs _
  have hintN : Integrable (fun n : upperUnipotent (t + 1) F => f (n.val * g))
      (unipotentHaar F t) :=
    integrable_subgroup_mul_of_hasCompactSupport _ (UpperUnipotent.isClosed (R := F)) _ f hfc
      hfs g
  have hΦ : Measurable (coordinates (K := F) h) := (continuous_coordinates h).measurable
  have hfm : Measurable fun n : upperUnipotent (t + 1) F => ENNReal.ofReal (f (n.val * g)) :=
    (ENNReal.continuous_ofReal.comp (hfc.comp (continuous_subtype_val.mul continuous_const))).measurable
  calc ∫⁻ x, ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f (fiberPoint h F x g))
          ∂μR
      = ∫⁻ x, ∫⁻ b : blockUnipotent h F, ENNReal.ofReal (f (b.val * (upperRadical h F x * g)))
          ∂μH ∂μR := by
        refine lintegral_congr fun x => ?_
        exact ofReal_integral_eq_lintegral_ofReal (hint x)
          (Filter.Eventually.of_forall fun b => hf0 _)
    _ = ∫⁻ p, ENNReal.ofReal (f ((coordinates h p).val * g)) ∂(μH.prod μR) := by
        symm
        rw [lintegral_prod_symm (fun p => ENNReal.ofReal (f ((coordinates h p).val * g)))
          (hfm.comp hΦ).aemeasurable]
        simp only [coordinates_val, mul_assoc]
    _ = ∫⁻ n, ENNReal.ofReal (f (n.val * g)) ∂(Measure.map (coordinates h) (μH.prod μR)) :=
        (lintegral_map hfm hΦ).symm
    _ = μR {x | ∀ a c, x a c ∈ O} * ∫⁻ n, ENNReal.ofReal (f (n.val * g)) ∂unipotentHaar F t := by
        rw [map_coordinates_prod F h μH hμH μR, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hintN (Filter.Eventually.of_forall fun n => hf0 _)]
        rfl

omit [MeasurableSpace (GeneralLinear (t + 1) F)] [BorelSpace (GeneralLinear (t + 1) F)] in
/-- **Tower unfolding.** For a kernel with the radical fiber law and any measure `ν_N`,
the composite `κ ∘ₘ ν_N` integrates `H`-averages of a nonnegative test function to `c` times
the `ν_N`-integral of its `N`-average. -/
theorem lintegral_comp_quotientAverageReal
    (μH : Measure (blockUnipotent h F)) [μH.IsHaarMeasure] [IsMulRightInvariant μH]
    (hμH : μH {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} = 1)
    [IsMulRightInvariant (unipotentHaar F t)]
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μR.IsAddHaarMeasure]
    (κ : Kernel (LeftUnipotentQuotient t F) (BlockQuotient h F))
    (hκ : ∀ g : GeneralLinear (t + 1) F,
      κ (Quotient.mk _ g) = Measure.map (fun x => fiberPoint h F x g) μR)
    (νN : Measure (LeftUnipotentQuotient t F))
    (f : C_c(GeneralLinear (t + 1) F, ℝ)) (hf0 : ∀ y, 0 ≤ f y) :
    ∫⁻ z, ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f z) ∂(κ ∘ₘ νN) =
      μR {x | ∀ a c, x a c ∈ O} *
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal (upperUnipotent (t + 1) F)
          (unipotentHaar F t) f q) ∂νN := by
  have hHm : Measurable fun z =>
      ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f z) :=
    (ENNReal.continuous_ofReal.comp
      (continuous_quotientAverageReal _ (isClosed_blockUnipotent h F) μH f)).measurable
  have hNm : Measurable fun q => ENNReal.ofReal (quotientAverageReal (upperUnipotent (t + 1) F)
      (unipotentHaar F t) f q) :=
    (ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (UpperUnipotent.isClosed (R := F)) _ f)).measurable
  rw [Measure.lintegral_bind κ.measurable.aemeasurable hHm.aemeasurable, ← lintegral_const_mul _ hNm]
  refine lintegral_congr fun q => ?_
  induction q using Quotient.inductionOn with
  | h g =>
    rw [hκ g, lintegral_map hHm (continuous_fiberPoint_left h g).measurable]
    exact lintegral_fiberPoint_quotientAverageReal h μH hμH μR f f.continuous
      f.hasCompactSupport hf0 g

/-- **The normalized tower identity.** If `ν_N` and `ν_H` are compatible quotient measures
for the same Haar measure `μG` on `GL_(t+1)`, and `κ` has the radical fiber law for an
additive Haar measure `μR` whose integral-rectangle mass `c` is finite, then
`κ ∘ₘ ν_N = c • ν_H`. -/
theorem comp_eq_smul
    (μG : Measure (GeneralLinear (t + 1) F)) [IsFiniteMeasureOnCompacts μG]
    (μH : Measure (blockUnipotent h F)) [μH.IsHaarMeasure] [IsMulRightInvariant μH]
    (hμH : μH {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} = 1)
    [IsMulRightInvariant (unipotentHaar F t)]
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μR.IsAddHaarMeasure]
    (hc : μR {x | ∀ a c, x a c ∈ O} ≠ ⊤)
    (κ : Kernel (LeftUnipotentQuotient t F) (BlockQuotient h F))
    (hκ : ∀ g : GeneralLinear (t + 1) F,
      κ (Quotient.mk _ g) = Measure.map (fun x => fiberPoint h F x g) μR)
    (νN : Measure (LeftUnipotentQuotient t F))
    (hνN : IsCompatible (upperUnipotent (t + 1) F) μG (unipotentHaar F t) νN)
    (νH : Measure (BlockQuotient h F)) (hνH : IsCompatible (blockUnipotent h F) μG μH νH) :
    κ ∘ₘ νN = μR {x | ∀ a c, x a c ∈ O} • νH := by
  set c := μR {x | ∀ a c, x a c ∈ O} with hcdef
  have : μH.Regular := inferInstance
  have hL : ∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f z) ∂(κ ∘ₘ νN) =
        c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG := fun f hf0 => by
    rw [lintegral_comp_quotientAverageReal h μH hμH μR κ hκ νN f hf0,
      RecursiveIntegration.lintegral_quotientAverageReal _ μG _ νN hνN f f.continuous f.hasCompactSupport hf0]
  have hR : ∀ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f z) ∂(c • νH) =
        c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG := fun f hf0 => by
    rw [lintegral_smul_measure, smul_eq_mul,
      RecursiveIntegration.lintegral_quotientAverageReal _ μG _ νH hνH f f.continuous f.hasCompactSupport hf0]
  have hlift : ∀ φ : C_c(BlockQuotient h F, ℝ), (∀ q, 0 ≤ φ q) →
      ∃ f : C_c(GeneralLinear (t + 1) F, ℝ), (∀ y, 0 ≤ f y) ∧
        ∀ q, quotientAverageReal (blockUnipotent h F) μH f q = φ q := by
    intro φ hφ
    obtain ⟨f, hf, hf0⟩ := realQuotientPositiveLifting (blockUnipotent h F)
      (isClosed_blockUnipotent h F) μH φ
    refine ⟨f, hf0 hφ, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have hfin : IsFiniteMeasureOnCompacts (κ ∘ₘ νN) := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨u, hu1, -, hucs, hu01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(BlockQuotient h F, ℝ) := ⟨u, hucs⟩
    obtain ⟨f, hf0, hfavg⟩ := hlift φ fun q => (hu01 q).1
    calc (κ ∘ₘ νN) C = ∫⁻ q, C.indicator 1 q ∂(κ ∘ₘ νN) :=
          (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ q, ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f q)
            ∂(κ ∘ₘ νN) := by
          apply lintegral_mono
          intro q
          dsimp only
          rw [hfavg q]
          by_cases hq : q ∈ C
          · rw [Set.indicator_of_mem hq]
            change (1 : ENNReal) ≤ ENNReal.ofReal (u q)
            rw [hu1 hq, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hq]
            exact zero_le
      _ = c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG := hL f hf0
      _ < ⊤ := ENNReal.mul_lt_top hc.lt_top
          (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).lintegral_lt_top
  have : (κ ∘ₘ νN).Regular := inferInstance
  have : νH.Regular := hνH.regular
  have : (c • νH).Regular := Regular.smul hc
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro φ
  let φr : C_c(BlockQuotient h F, ℝ) :=
    ⟨⟨fun q => (φ q : ℝ), NNReal.continuous_coe.comp φ.continuous⟩,
      φ.hasCompactSupport.comp_left NNReal.coe_zero⟩
  obtain ⟨f, hf0, hfavg⟩ := hlift φr fun q => (φ q).coe_nonneg
  have key : ∀ μ' : Measure (BlockQuotient h F),
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (blockUnipotent h F) μH f q) ∂μ' =
        c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG →
      ∫ q, (φ q : ℝ) ∂μ' = (c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG).toReal := by
    intro μ' h'
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => (φ q).coe_nonneg)
      (NNReal.continuous_coe.comp φ.continuous).aestronglyMeasurable, ← h']
    congr 1
    apply lintegral_congr
    intro q
    rw [hfavg q]
    rfl
  rw [key _ (hL f hf0), key _ (hR f hf0)]

omit [T2Space F] [MeasurableSpace (GeneralLinear (t + 1) F)] [BorelSpace (GeneralLinear (t + 1) F)]
  [MeasurableSpace (blockUnipotent h F)] [BorelSpace (blockUnipotent h F)]
  [MeasurableSpace (upperUnipotent (t + 1) F)] [BorelSpace (upperUnipotent (t + 1) F)] in
/-- **Restriction of the tower.** A kernel with the radical fiber law lives over the fibers of
`π : H \ G → N \ G`, so a scaled identity `κ ∘ₘ ν_N = c • ν_H` restricts to
`κ ∘ₘ ν_N|_s = c • ν_H|_(π⁻¹ s)` for every measurable `s`. -/
theorem comp_restrict_eq_smul
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (κ : Kernel (LeftUnipotentQuotient t F) (BlockQuotient h F))
    (hκ : ∀ g : GeneralLinear (t + 1) F,
      κ (Quotient.mk _ g) = Measure.map (fun x => fiberPoint h F x g) μR)
    (νN : Measure (LeftUnipotentQuotient t F)) (νH : Measure (BlockQuotient h F)) (c : ℝ≥0∞)
    (hκν : κ ∘ₘ νN = c • νH) (s : Set (LeftUnipotentQuotient t F)) (hs : MeasurableSet s) :
    κ ∘ₘ νN.restrict s = c • νH.restrict (projection h F ⁻¹' s) := by
  have hπ : Measurable (projection h F) := (continuous_projection' h).measurable
  have hpt : ∀ A, MeasurableSet A → ∀ q,
      κ q (A ∩ projection h F ⁻¹' s) = s.indicator (fun q => κ q A) q := by
    intro A hA q
    induction q using Quotient.inductionOn with
    | h g =>
      have hfm := (continuous_fiberPoint_left h g).measurable
      rw [hκ g, Measure.map_apply hfm (hA.inter (hπ hs))]
      by_cases hq : (Quotient.mk _ g : LeftUnipotentQuotient t F) ∈ s
      · rw [Set.indicator_of_mem hq, hκ g, Measure.map_apply hfm hA]
        congr 1
        ext x
        simp [projection_fiberPoint, hq]
      · rw [Set.indicator_of_notMem hq]
        have he : (fun x => fiberPoint h F x g) ⁻¹' (A ∩ projection h F ⁻¹' s) = ∅ := by
          ext x
          simp [projection_fiberPoint, hq]
        rw [he, measure_empty]
  ext A hA
  rw [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, ← lintegral_indicator hs,
    show (∫⁻ q, s.indicator (fun q => κ q A) q ∂νN) =
      ∫⁻ q, κ q (A ∩ projection h F ⁻¹' s) ∂νN from lintegral_congr fun q => (hpt A hA q).symm,
    ← Measure.bind_apply (hA.inter (hπ hs)) κ.measurable.aemeasurable]
  rw [hκν, Measure.smul_apply, smul_eq_mul]

end Tower

/-! ### The tail of the statement over a `p`-adic field -/

/-- **The tail of `TwoBlockUnipotentQuotientIntegrationStatement`.** Over a `p`-adic field
with the statement's topology and Borel structures, take the statement's measures `μG`, `μN`
and the fixed block measure `μH`, with `μH` Haar and `μN`, `μH` right invariant. Then for every
additive Haar measure `μR` whose integral-rectangle mass `c` satisfies `c ≠ 0` and `c ≠ ⊤`,
and every s-finite kernel `κ` with the radical fiber law, every compatible pair `ν_N`, `ν_H`
is σ-finite. Over every measurable `s` the pair satisfies the restricted measure identity,
the Tonelli identity, and the absolute-integrability and Bochner laws. -/
abbrev TowerTailStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1),
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    let G := GeneralLinear (t + 1) F.Carrier
    let N := upperUnipotent (t + 1) F.Carrier
    let H := blockUnipotent h F.Carrier
    let NQ := LeftUnipotentQuotient t F.Carrier
    let HQ := BlockQuotient h F.Carrier
    let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace H := borel H
    letI : BorelSpace H := ⟨rfl⟩
    letI : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F.Carrier) :=
      fun i => borel (upperUnipotent (m i + 1) F.Carrier)
    letI : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F.Carrier) :=
      fun _ => ⟨rfl⟩
    letI : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F.Carrier) :=
      fun i => by
        let := T.generalLinearSecondCountableTopology (m i + 1)
        exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μN : Measure N := unipotentHaar F.Carrier t
    let μH : Measure H := Measure.map (blockUnipotentEquiv h F.Carrier)
      (Measure.pi (fun i : Fin 2 => unipotentHaar F.Carrier (m i)))
    ∀ [μH.IsHaarMeasure] [Measure.IsMulRightInvariant μN] [Measure.IsMulRightInvariant μH]
      (μR : Measure R) [μR.IsAddHaarMeasure],
      let O := (ValuativeRel.valuation F.Carrier).integer
      let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ O}
      c ≠ 0 → c ≠ ⊤ →
      ∀ (κ : Kernel NQ HQ) [IsSFiniteKernel κ],
        (∀ g : G, κ (Quotient.mk _ g) =
          Measure.map (fun x => fiberPoint h F.Carrier x g) μR) →
        ∀ (νN : Measure NQ) (νH : Measure HQ),
          IsCompatible N μG μN νN → IsCompatible H μG μH νH →
          SigmaFinite νN ∧ SigmaFinite νH ∧
          ∀ s : Set NQ, MeasurableSet s →
            let νNs := νN.restrict s
            let νHs := νH.restrict (projection h F.Carrier ⁻¹' s)
            (κ ∘ₘ νNs = c • νHs) ∧
            (∀ f : HQ → ℝ≥0∞, Measurable f →
              (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νNs) = c * ∫⁻ z, f z ∂νHs) ∧
            (∀ f : HQ → ℂ, Measurable f →
              (Integrable f νHs ↔
                (∀ᵐ q ∂νNs, Integrable f (κ q)) ∧
                Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νNs) ∧
              (Integrable f νHs →
                Integrable (radicalAverage F h μR f) νNs ∧
                (∫ q, radicalAverage F h μR f q ∂νNs) =
                  c.toReal • (∫ z, f z ∂νHs)))

/-- Proof of `TowerTailStatement`: `comp_eq_smul` gives `κ ∘ₘ ν_N = c • ν_H`, regular
measures on the σ-compact quotients are σ-finite, `comp_restrict_eq_smul` restricts the
identity, and `analytic_of_comp_eq_smul` gives the analytic conjuncts. -/
theorem tail_of_fiberLaw : TowerTailStatement.{uF} := by
  intro p _ F t m h T G N H NQ HQ R μG μN μH _ _ _ μR _ O c hc0 hc κ _ hκ νN νH hνN hνH
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (t + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (t + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (blockUnipotent h F.Carrier) := borel _
  let : BorelSpace (blockUnipotent h F.Carrier) := ⟨rfl⟩
  let : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => borel (upperUnipotent (m i + 1) F.Carrier)
  let : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F.Carrier) := fun _ => ⟨rfl⟩
  let : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => by
      let := T.generalLinearSecondCountableTopology (m i + 1)
      exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace (LeftUnipotentQuotient t F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (BlockQuotient h F.Carrier) := borel _
  let : BorelSpace (BlockQuotient h F.Carrier) := ⟨rfl⟩
  have hμH : μH {b : blockUnipotent h F.Carrier |
      b.val ∈ Conductor.integralSubgroup (Valuation.integer (ValuativeRel.valuation F.Carrier)) t}
      = 1 :=
    blockMeasure_integral F.Carrier h
  have hκν : κ ∘ₘ νN = c • νH := comp_eq_smul h μG μH hμH μR hc κ hκ νN hνN νH hνH
  have : νN.Regular := hνN.regular
  have : νH.Regular := hνH.regular
  have hσN : SigmaFinite νN := inferInstance
  have hσH : SigmaFinite νH := inferInstance
  refine ⟨hσN, hσH, fun s hs => ?_⟩
  have hs' := comp_restrict_eq_smul h μR κ hκ νN νH c hκν s hs
  exact ⟨hs', TwoBlockUnipotentQuotient.analytic_of_comp_eq_smul F h μR c hc0 hc κ hκ
    (νN.restrict s) (νH.restrict (projection h F.Carrier ⁻¹' s)) hs'⟩

end Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration
