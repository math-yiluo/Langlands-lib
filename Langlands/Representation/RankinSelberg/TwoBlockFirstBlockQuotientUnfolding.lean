import Langlands.Analysis.Local.QuotientWeilKernel
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockMeasures

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
open scoped ENNReal CompactlySupported ProbabilityTheory

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance unfoldingInst1 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance unfoldingInst2 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance unfoldingInst3 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance unfoldingInst4 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance unfoldingInst5 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance unfoldingInst6 : MeasurableSpace F.Carrier := borel _
local instance unfoldingInst7 : BorelSpace F.Carrier := ⟨rfl⟩
local instance unfoldingInst8 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance unfoldingInst9 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance unfoldingInst10 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance unfoldingInst11 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance unfoldingInst12 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance unfoldingInst13 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance unfoldingInst14 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance unfoldingInst15 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance unfoldingInst16 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance unfoldingInst17 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance unfoldingInst18 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance unfoldingInst19 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance unfoldingInst20 (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance unfoldingInst21 (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance unfoldingInst22 (n : ℕ) : SecondCountableTopology (LeftUnipotentQuotient n F.Carrier) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance unfoldingInst23 : MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := borel _
local instance unfoldingInst24 : BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance unfoldingInst25 : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := borel _
local instance unfoldingInst26 : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance unfoldingInst27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance unfoldingInst28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance unfoldingInst29 : MeasurableSpace (MixedQuotient F h) := borel _
local instance unfoldingInst30 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

/-- The small orbital measure retains the exact determinant-zero restriction. -/
abbrev SmallOrbitKernelRestrictionStatement (n : ℕ)
    (νA : Measure (LeftUnipotentQuotient n F.Carrier)) : Prop :=
    IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) νA →
    orbitKernel (upperUnipotent (n + 1) F.Carrier) (UpperUnipotent.isClosed (R := F.Carrier))
        (unipotentHaar F.Carrier n) ∘ₘ
      νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData n 0) =
        Measure.map Subtype.val (normOneHaar F n)

theorem small_orbitKernel_comp_zero (n : ℕ)
    (νA : Measure (LeftUnipotentQuotient n F.Carrier))
    (hνA : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) νA) :
    orbitKernel (upperUnipotent (n + 1) F.Carrier) (UpperUnipotent.isClosed (R := F.Carrier))
        (unipotentHaar F.Carrier n) ∘ₘ
      νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData n 0) =
        Measure.map Subtype.val (normOneHaar F n) := by
  let N := upperUnipotent (n + 1) F.Carrier
  let κ := orbitKernel N (UpperUnipotent.isClosed (R := F.Carrier)) (unipotentHaar F.Carrier n)
  let s := RankinSelberg.determinantSlice F.canonicalTopologicalData n 0
  let π : GeneralLinear (n + 1) F.Carrier → LeftUnipotentQuotient n F.Carrier := Quotient.mk _
  have hs : MeasurableSet s := RankinSelberg.isClosed_determinantSlice _ n 0 |>.measurableSet
  have hπ : Measurable π := continuous_quotient_mk'.measurable
  have hpt : ∀ A, MeasurableSet A → ∀ q,
      κ q (A ∩ π ⁻¹' s) = s.indicator (fun q => κ q A) q := by
    intro A hA q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [show κ (Quotient.mk _ g) = _ from orbitKernel_mk N _ _ g,
        Measure.map_apply (continuous_subtype_val.mul_const g).measurable (hA.inter (hπ hs))]
      have he : ∀ a : N, π (a.val * g) = π g := fun a =>
        TwoBlockUnipotentQuotient.mk_mul_of_mem N a.property g
      by_cases hq : π g ∈ s
      · rw [Set.indicator_of_mem hq, show κ (Quotient.mk _ g) = _ from orbitKernel_mk N _ _ g,
          Measure.map_apply (continuous_subtype_val.mul_const g).measurable hA]
        congr 1
        ext a
        simp [he, hq]
      · rw [Set.indicator_of_notMem hq]
        have hempty : (fun a : N => a.val * g) ⁻¹' (A ∩ π ⁻¹' s) = ∅ := by
          ext a
          simp [he, hq]
        rw [hempty, measure_empty]
  have hcomp : κ ∘ₘ νA.restrict s = (generalLinearHaar F.Carrier n).restrict (π ⁻¹' s) := by
    ext A hA
    rw [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.restrict_apply hA,
      ← lintegral_indicator hs]
    rw [show (∫⁻ q, s.indicator (fun q => κ q A) q ∂νA) =
      ∫⁻ q, κ q (A ∩ π ⁻¹' s) ∂νA from
        lintegral_congr fun q => (hpt A hA q).symm]
    rw [← Measure.bind_apply (hA.inter (hπ hs)) κ.measurable.aemeasurable,
      show κ ∘ₘ νA = generalLinearHaar F.Carrier n from
        orbitKernel_comp N (UpperUnipotent.isClosed (R := F.Carrier)) _ _ νA hνA]
  have hs0 : π ⁻¹' s = (normOneSubgroup F (n + 1) : Set _) := by
    ext u
    change F.canonicalTopologicalData.ord (GeneralLinear.determinant u : F.Carrier) = 0 ↔ _
    rw [PadicField.TopologicalData.ord_eq_zero_iff_normalizedAbs,
      Matrix.GeneralLinearGroup.val_det_apply,
      ← mem_normOneSubgroup_iff_normalizedAbs]
    rfl
  rw [map_normOneHaar, ← hs0]
  exact hcomp

/-- The fixed block measure unfolds into its two specified unipotent measures. -/
theorem lintegral_blockHaar (f : TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ b, f b ∂TwoBlockUnipotentQuotient.blockHaar F.Carrier h =
      ∫⁻ a : upperUnipotent (m 0 + 1) F.Carrier,
        ∫⁻ b : upperUnipotent (m 1 + 1) F.Carrier,
          f (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F.Carrier
            ((MeasurableEquiv.piFinTwo _).symm (a, b)))
          ∂unipotentHaar F.Carrier (m 1) ∂unipotentHaar F.Carrier (m 0) := by
  let e := MeasurableEquiv.piFinTwo (fun i : Fin 2 => upperUnipotent (m i + 1) F.Carrier)
  have hm : Measurable (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F.Carrier) :=
    (TwoBlockUnipotentQuotient.blockUnipotentHomeomorph h F.Carrier).continuous.measurable
  rw [TwoBlockUnipotentQuotient.blockHaar, lintegral_map hf hm]
  have hpi := measurePreserving_piFinTwo (fun i : Fin 2 => unipotentHaar F.Carrier (m i))
  have he := hpi.symm e
  have hfm : Measurable (fun x => f (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F.Carrier
      (e.symm x))) := hf.comp (hm.comp e.symm.measurable)
  have hfe : Measurable (fun x => f (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F.Carrier x)) :=
    hf.comp hm
  rw [← he.lintegral_comp hfe, lintegral_prod _ hfm.aemeasurable]

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
