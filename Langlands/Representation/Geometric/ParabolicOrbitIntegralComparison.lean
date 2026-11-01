import Langlands.Representation.Geometric.ParabolicOrbitCompactComparison

/-! The actual orbit comparison with supplied compatible measures. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open GeneralLinear Induction MeasureTheory MeasureTheory.Measure QuotientIntegration

universe uF

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

local instance : MeasurableSpace (parabolicOrbitStagesRetraction F B C w).ker := borel _
local instance : BorelSpace (parabolicOrbitStagesRetraction F B C w).ker := ⟨rfl⟩
local instance : MeasurableSpace (parabolicOrbitNestedIntersection F B C w) := borel _
local instance : BorelSpace (parabolicOrbitNestedIntersection F B C w) := ⟨rfl⟩
local instance : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F B C w)) := borel _
local instance : BorelSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F B C w)) := ⟨rfl⟩

/-- Supplied actual two-sided regular Haar measures and their compatible
locally finite quotient measure on the actual nested orbit kernel. -/
structure ParabolicOrbitIntegralMeasures where
  kernel : Measure (parabolicOrbitStagesRetraction F B C w).ker
  intersection : Measure (parabolicOrbitNestedIntersection F B C w)
  quotient : Measure (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F B C w))
  kernelHaar : IsHaarMeasure kernel
  kernelRegular : kernel.Regular
  kernelRight : IsMulRightInvariant kernel
  intersectionHaar : IsHaarMeasure intersection
  intersectionRegular : intersection.Regular
  intersectionRight : IsMulRightInvariant intersection
  quotientFinite : IsFiniteMeasureOnCompacts quotient
  compatible : letI := intersectionRight
    IsCompatible (parabolicOrbitNestedIntersection F B C w) kernel intersection quotient

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Induction MeasureTheory QuotientIntegration HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- Existence supplies the full actual measure data, independently of any
coefficient representation. -/
theorem parabolicOrbitIntegralMeasures_nonempty :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    Nonempty (ParabolicOrbitIntegralMeasures F.Carrier B C w) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hm := T.parabolicOrbitNested_measureExists B C w
  dsimp only at hm
  obtain ⟨μN, μI, hμN, hμNr, hμNri, hμI, hμIr, hμIri, ν, hν, hc⟩ := hm
  exact ⟨⟨μN, μI, ν, hμN, hμNr, hμNri, hμI, hμIr, hμIri, hν, hc⟩⟩

/-- The actual compact orbit equivalence using exactly the supplied compatible
measure data. The integrated coefficient is the existing Haar-ratio coefficient. -/
def parabolicOrbitCompactIntegralEquiv :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ParabolicOrbitIntegralMeasures F.Carrier B C w →
      ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        (Parabolic.leviCoinvariants C
          (compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
            (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
              A.representation))).Equiv
          (compactInduced (parabolicOrbitStagesQuotient F.Carrier B C w)
            (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
              A.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.parabolicLocallyCompactSpace C
  let : MeasurableSpace (parabolicOrbitStagesRetraction F.Carrier B C w).ker := borel _
  let : BorelSpace (parabolicOrbitStagesRetraction F.Carrier B C w).ker := ⟨rfl⟩
  let : MeasurableSpace (parabolicOrbitNestedIntersection F.Carrier B C w) := borel _
  let : BorelSpace (parabolicOrbitNestedIntersection F.Carrier B C w) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
  let : BorelSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := ⟨rfl⟩
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace (parabolicOrbitStagesRetraction F.Carrier B C w).ker :=
    (parabolicOrbitNestedRadicalEquiv F.Carrier B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  intro m A
  let := m.kernelHaar
  let := m.kernelRegular
  let := m.kernelRight
  let := m.intersectionHaar
  let := m.intersectionRegular
  let := m.intersectionRight
  let := m.quotientFinite
  have hσ : IsSmooth (parabolicOrbitCoefficient F.Carrier B C w
      (T.leviHalfModulus B) A.representation) :=
    isSmooth_comp (parabolicOrbitToSourceLevi F.Carrier B C w)
      (continuous_parabolicOrbitToSourceLevi F.Carrier B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) A.representation
        (T.isOpen_ker_leviHalfModulus B)).mpr A.isSmooth)
  have hN : IsClosed ((C.leviProjection F.Carrier).ker :
      Set (C.parabolic F.Carrier)) :=
    isClosed_singleton.preimage (C.leviProjectionContinuous F.Carrier).continuous
  exact (splitStagesCompactEquiv
    (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
    (C.leviProjection_section F.Carrier)
    (C.leviProjectionContinuous F.Carrier).continuous
    (C.leviInParabolicContinuous F.Carrier).continuous
    (parabolicOrbitStages F.Carrier B C w)
    (parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_kernel_le F.Carrier B C w)
    (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
    (isClosed_parabolicOrbitStages F.Carrier B C w)
    (isClosed_parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_section_mem F.Carrier B C w)
    (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) A.representation)
    hσ m.quotient (T.parabolicOrbitNestedKernel_compactOpenBasis B C w)
    m.kernel m.intersection m.compatible hN
    (T.parabolicOrbitParabolic_compactOpenBasis C)).trans
      (compactInducedEquiv (parabolicOrbitStagesQuotient F.Carrier B C w)
        (parabolicOrbitIntegratedCoefficientEquiv F.Carrier B C w (T.leviHalfModulus B)
          A.representation))

/-- The genuine compact stages kernel slice for an arbitrary smooth source
coefficient. Its evaluation is the original orbit function at `x * s(l)`. -/
def parabolicOrbitIntegralKernelSlice :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
            A.representation) →
        C.Levi F.Carrier →
          CompactFunctions (parabolicOrbitNestedIntersection F.Carrier B C w)
            (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B)
              A.representation) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.parabolicLocallyCompactSpace C
  intro A
  have hσ : IsSmooth (parabolicOrbitCoefficient F.Carrier B C w
      (T.leviHalfModulus B) A.representation) :=
    isSmooth_comp (parabolicOrbitToSourceLevi F.Carrier B C w)
      (continuous_parabolicOrbitToSourceLevi F.Carrier B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) A.representation
        (T.isOpen_ker_leviHalfModulus B)).mpr A.isSmooth)
  exact splitStagesKernelSlice
    (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
    (C.leviProjection_section F.Carrier)
    (C.leviProjectionContinuous F.Carrier).continuous
    (C.leviInParabolicContinuous F.Carrier).continuous
    (parabolicOrbitStages F.Carrier B C w)
    (parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_kernel_le F.Carrier B C w)
    (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
    (isClosed_parabolicOrbitStages F.Carrier B C w)
    (isClosed_parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_section_mem F.Carrier B C w)
    (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) A.representation)
    hσ

/-- The actual compactly supported simple function integrated at a Levi point. -/
def parabolicOrbitIntegralIntegrand :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
            A.representation) →
        C.Levi F.Carrier →
          SimpleFunc (QuotientIntegration.LeftQuotient
            (parabolicOrbitNestedIntersection F.Carrier B C w))
            (Representation.Coinvariants (parabolicOrbitNestedCoefficient
              F.Carrier B C w (T.leviHalfModulus B) A.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
  let : BorelSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := ⟨rfl⟩
  intro A f l
  exact quotientCoinvariantSimple _ _ (T.parabolicOrbitIntegralKernelSlice B C w A f l)

@[simp]
theorem parabolicOrbitIntegralIntegrand_mk :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (f : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
          A.representation))
      (l : C.Levi F.Carrier) (x : (parabolicOrbitStagesRetraction F.Carrier B C w).ker),
      T.parabolicOrbitIntegralIntegrand B C w A f l
          (quotientMap (parabolicOrbitNestedIntersection F.Carrier B C w) x) =
        Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B)
            A.representation)
          (eval _ _ f.val (x.val.val * C.leviInParabolic F.Carrier l)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A f l x
  rfl

/-- Its value on every actual compact representative is the integral of the
actual compact stages integrand for the supplied quotient measure. -/
theorem parabolicOrbitCompactIntegralEquiv_eval_mk :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    ∀ (m : ParabolicOrbitIntegralMeasures F.Carrier B C w)
      (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (f : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
          A.representation))
      (l : C.Levi F.Carrier),
      eval (parabolicOrbitStagesQuotient F.Carrier B C w)
          (parabolicOrbitIntegratedCoefficient F.Carrier B C w
            (T.leviHalfModulus B) A.representation)
          (T.parabolicOrbitCompactIntegralEquiv B C w m A
            (Representation.Coinvariants.mk
              ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
                (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
                  A.representation)).comp (C.leviProjection F.Carrier).ker.subtype)
              f)).val l =
        AlgebraicIntegral.integral m.quotient
          (T.parabolicOrbitIntegralIntegrand B C w A f l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.parabolicLocallyCompactSpace C
  let : MeasurableSpace (parabolicOrbitStagesRetraction F.Carrier B C w).ker := borel _
  let : BorelSpace (parabolicOrbitStagesRetraction F.Carrier B C w).ker := ⟨rfl⟩
  let : MeasurableSpace (parabolicOrbitNestedIntersection F.Carrier B C w) := borel _
  let : BorelSpace (parabolicOrbitNestedIntersection F.Carrier B C w) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
  let : BorelSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := ⟨rfl⟩
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace (parabolicOrbitStagesRetraction F.Carrier B C w).ker :=
    (parabolicOrbitNestedRadicalEquiv F.Carrier B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  intro m A f l
  let := m.kernelHaar
  let := m.kernelRegular
  let := m.kernelRight
  let := m.intersectionHaar
  let := m.intersectionRegular
  let := m.intersectionRight
  let := m.quotientFinite
  have hσ : IsSmooth (parabolicOrbitCoefficient F.Carrier B C w
      (T.leviHalfModulus B) A.representation) :=
    isSmooth_comp (parabolicOrbitToSourceLevi F.Carrier B C w)
      (continuous_parabolicOrbitToSourceLevi F.Carrier B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) A.representation
        (T.isOpen_ker_leviHalfModulus B)).mpr A.isSmooth)
  have h := splitStagesCompactEquiv_eval_mk_integral
    (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
    (C.leviProjection_section F.Carrier)
    (C.leviProjectionContinuous F.Carrier).continuous
    (C.leviInParabolicContinuous F.Carrier).continuous
    (parabolicOrbitStages F.Carrier B C w)
    (parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_kernel_le F.Carrier B C w)
    (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
    (isClosed_parabolicOrbitStages F.Carrier B C w)
    (isClosed_parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_section_mem F.Carrier B C w)
    (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) A.representation)
    hσ m.quotient (T.parabolicOrbitNestedKernel_compactOpenBasis B C w)
    m.kernel m.intersection m.compatible
    (isClosed_singleton.preimage (C.leviProjectionContinuous F.Carrier).continuous)
    (T.parabolicOrbitParabolic_compactOpenBasis C) f l
  exact h

end Langlands.PadicField.TopologicalData
