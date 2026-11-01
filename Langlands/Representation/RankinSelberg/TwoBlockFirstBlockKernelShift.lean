import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockSliceShift
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Determinant transport for the first-block fiber kernel
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
open scoped ENNReal

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance kernelShiftTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance kernelShiftValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance kernelShiftLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance kernelShiftFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance kernelShiftFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance kernelShiftGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance kernelShiftGLBorel (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance kernelShiftGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance kernelShiftGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance kernelShiftUnipotentMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance kernelShiftUnipotentBorel (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance kernelShiftSmallQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance kernelShiftSmallQuotientBorel (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

/-- Right translation carries the zero small slice to the prescribed slice exactly. -/
theorem map_restrict_smallSlice_of_ord (n : ℕ)
    (νA : Measure (LeftUnipotentQuotient n F.Carrier))
    (hνA : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) νA)
    (z : GeneralLinear (n + 1) F.Carrier) (k : ℤ)
    (hz : F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) = k) :
    Measure.map (rightTranslate _ z)
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData n 0)) =
      νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData n k) := by
  have hpre : rightTranslate _ z ⁻¹'
      RankinSelberg.determinantSlice F.canonicalTopologicalData n k =
      RankinSelberg.determinantSlice F.canonicalTopologicalData n 0 := by
    ext q
    rw [Set.mem_preimage,
      RankinSelberg.rightTranslate_mem_determinantSlice F.canonicalTopologicalData n k,
      hz, sub_self]
  have hp := (hνA.right_invariant z).restrict_preimage_emb
    (rightTranslate _ z).measurableEmbedding
    (RankinSelberg.determinantSlice F.canonicalTopologicalData n k)
  rw [hpre] at hp
  exact hp.map_eq

/-- Every integer occurs as the determinant order of a positive-rank matrix. -/
theorem exists_determinantOrder (n : ℕ) (k : ℤ) :
    ∃ z : GeneralLinear (n + 1) F.Carrier,
      F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) = k := by
  obtain ⟨x, hx, hxo⟩ := F.canonicalTopologicalData.ord_surjective_nonzero k
  obtain ⟨z, hz⟩ := Matrix.GeneralLinearGroup.det_surjective
    (n := Fin (n + 1)) (Units.mk0 x hx)
  refine ⟨z, ?_⟩
  change F.canonicalTopologicalData.ord (Matrix.GeneralLinearGroup.det z : F.Carrier) = k
  rw [hz]
  exact hxo

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance kernelShiftMixedQuotientMeasurable : MeasurableSpace (MixedQuotient F h) := borel _
local instance kernelShiftMixedQuotientBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance kernelShiftBlockQuotientMeasurable : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
  borel _
local instance kernelShiftBlockQuotientBorel : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance kernelShiftMixedMeasurable : MeasurableSpace (mixedSubgroup F h) := borel _
local instance kernelShiftMixedBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩

/-- Arbitrary first-block multiplication of the base is right translation of the fiber. -/
theorem fiberPoint_firstBlockEmbedding_mul
    (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (z : GeneralLinear (m 0 + 1) F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    fiberPoint h F.Carrier q (firstBlockEmbedding h F.Carrier z * g) =
      fiberPoint h F.Carrier (rightTranslate _ z q) g := by
  induction q using Quotient.inductionOn with
  | h u => rw [rightTranslate_mk, fiberPoint_mk, fiberPoint_mk, map_mul, mul_assoc]

variable (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
  (hInvariant : NormOneRightInvariant F (m 0) νA)
  (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)

include hνA

/-- The k-th fiber kernel is the zero kernel evaluated at the shifted outer point. -/
theorem fiberKernel_eq_zero_shift (z : GeneralLinear (m 0 + 1) F.Carrier) (k : ℤ)
    (hz : F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) = k)
    (q : MixedQuotient F h) :
    fiberKernel F h νA hInvariant k q =
      fiberKernel F h νA hInvariant 0 (mixedLeftShift F h z q) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mixedLeftShift_mk, fiberKernel_mk, fiberKernel_mk]
    have hf : Measurable (fun q => fiberPoint h F.Carrier q g) :=
      ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    simp_rw [fiberPoint_firstBlockEmbedding_mul]
    change _ = Measure.map ((fun q => fiberPoint h F.Carrier q g) ∘ rightTranslate _ z) _
    rw [← Measure.map_map hf (rightTranslate _ z).measurable,
      map_restrict_smallSlice_of_ord F (m 0) νA hνA z k hz]

/-- Kernel composition transports the inner k slice to the outer k slice. -/
theorem fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (mixedHaar F h) νL) (k : ℤ) :
    fiberKernel F h νA hInvariant k ∘ₘ (νL.restrict (determinantSlice F h 0)) =
      fiberKernel F h νA hInvariant 0 ∘ₘ (νL.restrict (determinantSlice F h k)) := by
  obtain ⟨z, hz⟩ := exists_determinantOrder F (m 0) k
  rw [← map_restrict_mixedLeftShift F h νL hνL z k hz]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (mixedLeftShift F h z).measurable]
  apply lintegral_congr
  intro q
  rw [fiberKernel_eq_zero_shift F h νA hInvariant hνA z k hz]

/-- The all-slices conclusion follows from zero-kernel disintegration on each outer slice. -/
theorem fiberKernel_comp_zeroSlice_eq
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (mixedHaar F h) νL)
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier))
    (hzero : ∀ k : ℤ, fiberKernel F h νA hInvariant 0 ∘ₘ
      (νL.restrict (determinantSlice F h k)) =
        νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k)) (k : ℤ) :
    fiberKernel F h νA hInvariant k ∘ₘ (νL.restrict (determinantSlice F h 0)) =
      νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k) := by
  rw [fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice F h νA hInvariant hνA νL hνL k,
    hzero k]

/-- Conditional fixed-zero-outer-slice disintegration after exact determinant transport. -/
def FirstBlockKernelShiftStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInvariant : NormOneRightInvariant F (m 0) νA),
    IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA →
    ∀ νL : Measure (MixedQuotient F h),
    IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t) (mixedHaar F h) νL →
    ∀ νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier),
    (∀ k : ℤ, fiberKernel F h νA hInvariant 0 ∘ₘ
      (νL.restrict (determinantSlice F h k)) =
        νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k)) →
    ∀ k : ℤ, fiberKernel F h νA hInvariant k ∘ₘ
      (νL.restrict (determinantSlice F h 0)) =
        νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k)

omit [Fact p.Prime] [SFinite νA] hνA in
/-- The conditional statement follows from the exact slice pushforwards. -/
theorem firstBlockKernelShift : FirstBlockKernelShiftStatement.{uF} := by
  intro p _ F t m h νA _ hInvariant hνA νL hνL νH hzero k
  exact fiberKernel_comp_zeroSlice_eq F h νA hInvariant hνA νL hνL νH hzero k

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
