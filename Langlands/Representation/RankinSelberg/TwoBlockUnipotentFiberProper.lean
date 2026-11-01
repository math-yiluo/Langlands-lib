import Langlands.Representation.RankinSelberg.TwoBlockUnipotentFiberKernel
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientCoordinates

/-!
# Compact finiteness and s-finiteness of the radical fiber kernel
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockUnipotentQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration TwoBlockJacquet
  TwoBlockDeformation TwoBlockUnipotentQuotientIntegration Set

universe uK uF

section Topology

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  [IsTopologicalGroup (GeneralLinear (t + 1) K)]
  [LocallyCompactSpace (GeneralLinear (t + 1) K)]

/-- Each radical fiber map has compact preimages of compact sets in the actual
block quotient. -/
theorem fiberPoint_isCompact_preimage (g : GeneralLinear (t + 1) K)
    {S : Set (BlockQuotient h K)} (hS : IsCompact S) :
    IsCompact ((fun x => fiberPoint h K x g) ⁻¹' S) := by
  let H := blockUnipotent h K
  let N := upperUnipotent (t + 1) K
  let := leftQuotient_t2Space H (isClosed_blockUnipotent h K)
  obtain ⟨C, hC, hCS⟩ := leftQuotient_exists_isCompact_image H
    (isClosed_blockUnipotent h K) hS
  let D : Set N := Subtype.val ⁻¹' ((fun c => c * g⁻¹) '' C)
  have hD : IsCompact D :=
    (UpperUnipotent.isClosed (R := K) (n := t + 1)).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hC.image (continuous_id.mul continuous_const))
  have himage : IsCompact (radicalCoord h '' D) := hD.image (continuous_radicalCoord h)
  have hf : Continuous (fun x => fiberPoint h K x g) :=
    continuous_quotient_mk'.comp ((continuous_upperRadical h K).mul continuous_const)
  refine himage.of_isClosed_subset (hS.isClosed.preimage hf) ?_
  intro x hx
  have hxC : fiberPoint h K x g ∈ leftQuotientMap H '' C := by rwa [hCS]
  obtain ⟨c, hc, hcx⟩ := hxC
  have hb : c * (upperRadical h K x * g)⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hcx.symm)
  let b := c * (upperRadical h K x * g)⁻¹
  have hn : c * g⁻¹ = b * upperRadical h K x := by
    dsimp [b]
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hnN : c * g⁻¹ ∈ N := by
    rw [hn]
    exact mul_mem (blockUnipotent_le_upperUnipotent h K hb)
      (upperRadical_mem_upperUnipotent h K x)
  let n : N := ⟨c * g⁻¹, hnN⟩
  refine ⟨n, ⟨c, hc, rfl⟩, ?_⟩
  have he : n = coordinates h (⟨b, hb⟩, x) := Subtype.ext hn
  rw [he, radicalCoord_coordinates]

end Topology

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Every fiber of the actual radical kernel is finite on compact sets. -/
theorem fiberKernel_compact_ne_top :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      [MeasurableSpace (GeneralLinear (t + 1) F.Carrier)]
      [BorelSpace (GeneralLinear (t + 1) F.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
      [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
      [MeasurableSpace (BlockQuotient h F.Carrier)] [BorelSpace (BlockQuotient h F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μ.IsAddHaarMeasure] (q : LeftUnipotentQuotient t F.Carrier)
      (S : Set (BlockQuotient h F.Carrier)), IsCompact S →
      fiberKernel F h μ q S ≠ ⊤ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  intro _ _ _ _ _ _ _ _ μ _ q S hS
  let : LocallyCompactSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F.Carrier))
  let := leftQuotient_t2Space (blockUnipotent h F.Carrier) (isClosed_blockUnipotent h F.Carrier)
  refine Quotient.inductionOn q fun g => ?_
  have hf : Measurable (fun x => fiberPoint h F.Carrier x g) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [fiberKernel_mk F h μ g, Measure.map_apply hf hS.measurableSet]
  exact (fiberPoint_isCompact_preimage h g hS).measure_ne_top

/-- S-finiteness of the actual radical kernel for every supplied rectangular Haar. -/
def FiberKernelSFiniteStatement : Prop :=
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      [MeasurableSpace (GeneralLinear (t + 1) F.Carrier)]
      [BorelSpace (GeneralLinear (t + 1) F.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
      [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
      [MeasurableSpace (BlockQuotient h F.Carrier)] [BorelSpace (BlockQuotient h F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μ.IsAddHaarMeasure],
      IsSFiniteKernel (fiberKernel F h μ)

/-- Compact finiteness and a common countable compact cover of the block quotient
prove s-finiteness of the measurable radical kernel. -/
theorem fiberKernel_isSFinite : FiberKernelSFiniteStatement F h := by
  unfold FiberKernelSFiniteStatement
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  intro _ _ _ _ _ _ _ _ μ _
  let H := blockUnipotent h F.Carrier
  let := leftQuotient_t2Space H (isClosed_blockUnipotent h F.Carrier)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (fiberKernel F h μ)
    (fiberKernel_compact_ne_top F h μ)

end Canonical

end Langlands.RankinSelberg.TwoBlockUnipotentQuotient
