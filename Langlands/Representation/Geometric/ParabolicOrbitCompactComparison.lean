import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Geometric.ParabolicOrbitHaarRatio
import Langlands.Representation.Geometric.ParabolicOrbitMeasureData
import Langlands.Representation.Geometric.ParabolicOrbitJacquet
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Geometric.ParabolicOrbitInductionTransport

/-! Specialization of the actual relative integral to the parabolic orbit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open GeneralLinear Induction MeasureTheory

universe uF uV uW

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] {n : ℕ} [LocallyCompactSpace (GeneralLinear n F)]
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local instance : LocallyCompactSpace (C.unipotentSubgroup F) :=
  (C.isClosed_unipotentSubgroup F).locallyCompactSpace
local instance : LocallyCompactSpace (parabolicOrbitStagesRetraction F B C w).ker :=
  (parabolicOrbitNestedKernelAmbientEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance : MeasurableSpace (parabolicOrbitStagesRetraction F B C w).ker :=
  borel _
local instance : BorelSpace (parabolicOrbitStagesRetraction F B C w).ker := ⟨rfl⟩
local instance : MeasurableSpace (parabolicOrbitNestedIntersection F B C w) := borel _
local instance : BorelSpace (parabolicOrbitNestedIntersection F B C w) := ⟨rfl⟩

/-- Identify the generic quotient character with the actual ambient Haar ratio. -/
def parabolicOrbitIntegratedCoefficientEquiv (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    (twist (Jacquet.complexCharacter
      (splitKernelHaarRatio (parabolicOrbitStagesRetraction F B C w)
        ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w))
        (parabolicOrbitNestedStabilizer F B C w)
        (parabolicOrbitNestedSection_mem F B C w)
        ((isClosed_parabolicOrbitStabilizer F B C w).preimage continuous_subtype_val)))
      (parabolicOrbitNestedCoefficientAction F B C w χ ρ)).Equiv
        (parabolicOrbitIntegratedCoefficient F B C w χ ρ) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' l := by
    rw [parabolicOrbitIntegratedCoefficient,
      parabolicOrbitStagesHaarRatio_eq_splitKernelHaarRatio F B C w]
    rfl


end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Induction MeasureTheory MeasureTheory.Measure CategoryTheory
open QuotientIntegration

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- One choice of actual quotient measures supplies a natural family of the
unnormalized compact orbit integral equivalences. -/
theorem parabolicOrbitCompactComparison_exists :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∃ E : ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      (Parabolic.leviCoinvariants C
        (compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
            A.representation))).Equiv
        (compactInduced (parabolicOrbitStagesQuotient F.Carrier B C w)
          (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
            A.representation)),
      ∀ (A A' : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) (f : A ⟶ A') z,
        E A' (Parabolic.leviCoinvariantsMap C
            (compactInducedMap (parabolicOrbitStabilizer F.Carrier B C w)
              (parabolicOrbitCoefficientMap F.Carrier B C w (T.leviHalfModulus B)
                (SmoothRep.hom f))) z) =
          compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w)
            (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w
              (T.leviHalfModulus B) (SmoothRep.hom f))
            (E A z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.parabolicLocallyCompactSpace C
  let N := (parabolicOrbitStagesRetraction F.Carrier B C w).ker
  let I := parabolicOrbitNestedIntersection F.Carrier B C w
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I := borel I
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel (QuotientIntegration.LeftQuotient I)
  let : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace N :=
    (parabolicOrbitNestedRadicalEquiv F.Carrier B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hm := T.parabolicOrbitNested_measureExists B C w
  dsimp only at hm
  obtain ⟨μN, μI, hμN, hμNr, hμNri, hμI, hμIr, hμIri, ν, hν, hc⟩ := hm
  let := hμN
  let := hμNr
  let := hμNri
  let := hμI
  let := hμIr
  let := hμIri
  let := hν
  have hσ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) :
      IsSmooth (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
        A.representation) :=
    isSmooth_comp (parabolicOrbitToSourceLevi F.Carrier B C w)
      (continuous_parabolicOrbitToSourceLevi F.Carrier B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) A.representation
        (T.isOpen_ker_leviHalfModulus B)).mpr A.isSmooth)
  have hN : IsClosed ((C.leviProjection F.Carrier).ker :
      Set (C.parabolic F.Carrier)) :=
    isClosed_singleton.preimage (C.leviProjectionContinuous F.Carrier).continuous
  let E := fun A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) =>
    splitStagesCompactEquiv
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
      (hσ A) ν (T.parabolicOrbitNestedKernel_compactOpenBasis B C w) μN μI hc hN
      (T.parabolicOrbitParabolic_compactOpenBasis C)
  let E' := fun A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) =>
    (E A).trans (compactInducedEquiv (parabolicOrbitStagesQuotient F.Carrier B C w)
      (parabolicOrbitIntegratedCoefficientEquiv F.Carrier B C w (T.leviHalfModulus B)
        A.representation))
  refine ⟨E', ?_⟩
  intro A A' f z
  have hn := splitStagesCompactEquiv_natural
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
    (hσ A) ν (T.parabolicOrbitNestedKernel_compactOpenBasis B C w) μN μI hc
    (hσ A') (parabolicOrbitCoefficientMap F.Carrier B C w (T.leviHalfModulus B)
      (SmoothRep.hom f)) hN (T.parabolicOrbitParabolic_compactOpenBasis C) z
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  have he := congrArg (fun q : CompactFunctions
      (parabolicOrbitStagesQuotient F.Carrier B C w)
      (twist (Jacquet.complexCharacter
        (splitKernelHaarRatio (parabolicOrbitStagesRetraction F.Carrier B C w)
          ((C.leviInParabolic F.Carrier).subgroupComap (parabolicOrbitStages F.Carrier B C w))
          (parabolicOrbitNestedStabilizer F.Carrier B C w)
          (parabolicOrbitNestedSection_mem F.Carrier B C w)
          ((isClosed_parabolicOrbitStabilizer F.Carrier B C w).preimage continuous_subtype_val)))
        (parabolicOrbitNestedCoefficientAction F.Carrier B C w (T.leviHalfModulus B)
          A'.representation)) => q.val.val.val l) hn
  exact he

end Langlands.PadicField.TopologicalData
