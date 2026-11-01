import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasureTransport

/-!
# Common measure package for the linked lower mixed quotient identities

The normalized subgroup measures admit all four required compatible quotients.
Every compatible choice is sigma-finite, including its prescribed lower transport.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerMeasurePackageInstance01 : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance lowerMeasurePackageInstance02 : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance lowerMeasurePackageInstance03 : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance lowerMeasurePackageInstance04 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance lowerMeasurePackageInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerMeasurePackageInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerMeasurePackageInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerMeasurePackageInstance08 (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerMeasurePackageInstance09 (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerMeasurePackageInstance10 (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerMeasurePackageInstance11 (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerMeasurePackageInstance12 (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerMeasurePackageInstance13 (n : ℕ) :
    MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerMeasurePackageInstance14 (n : ℕ) :
    BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerMeasurePackageInstance15 (n : ℕ) :
    SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasurePackageInstance16 (n : ℕ) :
    LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerMeasurePackageInstance17 (n : ℕ) :
    MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerMeasurePackageInstance18 (n : ℕ) :
    BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerMeasurePackageInstance19 (n : ℕ) :
    SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasurePackageInstance20 (n : ℕ) :
    LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerMeasurePackageInstance21 :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerMeasurePackageInstance22 :
    BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance23 :
    SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasurePackageInstance24 :
    LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerMeasurePackageInstance25 :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerMeasurePackageInstance26 :
    BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance27 :
    SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasurePackageInstance28 :
    LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace
local instance lowerMeasurePackageInstance29 :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerMeasurePackageInstance30 :
    BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance31 :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance lowerMeasurePackageInstance32 :
    BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance lowerMeasurePackageInstance33 (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance lowerMeasurePackageInstance34 (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance lowerMeasurePackageInstance35 :
    MeasurableSpace (lowerBlockUnipotent h F.Carrier) := borel _
local instance lowerMeasurePackageInstance36 :
    BorelSpace (lowerBlockUnipotent h F.Carrier) := ⟨rfl⟩
local instance lowerMeasurePackageInstance37 :
    MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance lowerMeasurePackageInstance38 :
    BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩

/-- Regular compatible measures on the closed quotients at hand are sigma-finite. -/
theorem compatibleQuotient_sigmaFinite
    (n : ℕ) (H : Subgroup (GeneralLinear (n + 1) F.Carrier))
    (hH : IsClosed (H : Set (GeneralLinear (n + 1) F.Carrier)))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μH : Measure H) [μH.IsMulRightInvariant]
    (ν : Measure (LeftQuotient H))
    (hν : IsCompatible H (generalLinearHaar F.Carrier n) μH ν) :
    SigmaFinite ν := by
  have : ν.Regular := hν.regular
  have : T2Space (LeftQuotient H) := leftQuotient_t2Space H hH
  have : LocallyCompactSpace (LeftQuotient H) := leftQuotient_locallyCompactSpace H
  have : SecondCountableTopology (LeftQuotient H) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap H)
  infer_instance

/-- The four prescribed standard and mixed quotient measures exist. -/
abbrev CompatibleExistenceStatement : Prop :=
  CompatibleMeasureExists (upperUnipotent (m 0 + 1) F.Carrier)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) ∧
  CompatibleMeasureExists (mixedSubgroup F h)
    (generalLinearHaar F.Carrier t) (mixedHaar F h) ∧
  CompatibleMeasureExists (lowerMixedSubgroup F h)
    (generalLinearHaar F.Carrier t) (lowerMixedHaar F h) ∧
  CompatibleMeasureExists (upperUnipotent (t + 1) F.Carrier)
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t)

/-- Existence uses the fixed measures, independently of every rectangular Haar. -/
theorem compatibleExistence : CompatibleExistenceStatement F h :=
  ⟨TwoBlockUnipotentQuotient.fullUnipotent_compatibleMeasureExists F.Carrier (m 0),
    mixed_compatibleMeasureExists F h, lowerMixed_compatibleMeasureExists F h,
    TwoBlockUnipotentQuotient.fullUnipotent_compatibleMeasureExists F.Carrier t⟩

/-- Every compatible choice has the required finiteness and exact lower transport. -/
abbrev CompatibleFinitenessStatement : Prop :=
  ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (νM : Measure (MixedQuotient F h))
    (νL : Measure (LowerMixedQuotient F h))
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)),
    IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA →
    IsCompatible (mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (mixedHaar F h) νM →
    IsCompatible (lowerMixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (lowerMixedHaar F h) νL →
    IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN →
    SigmaFinite νA ∧ SigmaFinite νM ∧ SigmaFinite νL ∧ SigmaFinite νN ∧
    IsCompatible (lowerBlockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (lowerHaar F h)
      (Measure.map (lowerToStandard h F.Carrier).symm νN) ∧
    SigmaFinite (Measure.map (lowerToStandard h F.Carrier).symm νN)

/-- Regularity on the second-countable locally compact closed quotients proves
sigma-finiteness; inverse conjugation and inverse left translation give compatibility. -/
theorem compatibleFiniteness : CompatibleFinitenessStatement F h := by
  intro νA νM νL νN hA hM hL hN
  have hσN := lowerMeasure_sigmaFinite F h νN hN
  exact ⟨compatibleQuotient_sigmaFinite F (m 0) _
      (UpperUnipotent.isClosed (R := F.Carrier)) _ νA hA,
    compatibleQuotient_sigmaFinite F t _ (isClosed_mixedSubgroup F h) _ νM hM,
    compatibleQuotient_sigmaFinite F t _ (isClosed_lowerMixedSubgroup F h) _ νL hL,
    hσN.1, lowerMeasure_isCompatible F h νN hN, hσN.2⟩

/-- The common existence, compatibility and sigma-finiteness package. -/
abbrev MeasurePackageStatement : Prop :=
  CompatibleExistenceStatement F h ∧ CompatibleFinitenessStatement F h

theorem measurePackage : MeasurePackageStatement F h :=
  ⟨compatibleExistence F h, compatibleFiniteness F h⟩

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
