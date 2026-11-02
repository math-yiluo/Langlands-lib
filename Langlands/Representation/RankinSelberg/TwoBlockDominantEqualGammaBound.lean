import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualGammaComparison

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  Polynomial TwoBlockJacquet LocalFactor TwoBlockLowerUnipotentQuotient
open scoped NNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalGammaBoundTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalGammaBoundValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalGammaBoundLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalGammaBoundT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalGammaBoundMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalGammaBoundBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalGammaBoundGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalGammaBoundGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaBoundUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalGammaBoundUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaBoundQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalGammaBoundQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)]
  [∀ i, Module ℂ (W i)]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- A complete certified gamma product for every sufficiently large real
opposite twist of the actual ordered block family. -/
def EqualTwoBlockSymmetricGammaBound : Prop :=
  ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
    EqualTwoBlockSymmetricGammaProduct F h ψ ν π
      (twoBlockOppositeTwistBlocks F m τ u)

set_option maxHeartbeats 1600000 in
/-- Choose the nonzero functionals and canonical compatible measures internally;
the retained actual comparison gives the large-twist certified gamma product. -/
theorem exists_equalTwoBlockSymmetricGammaProduct
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) :
    EqualTwoBlockSymmetricGammaBound F h ψ ν π τ := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 0)
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 1)
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  have hex : ∀ i, ∃ ell : glInverseFunctionals ψ (m i) (τ i), ell.val ≠ 0 :=
    fun i => ((isOfWhittakerType_standard_iff_inverse ψ (τ i)).mp (hτ i)).exists_ne_zero
  choose ell0 hell0 using hex
  obtain ⟨Cbound, hCbound⟩ := exists_equalTwoBlockRationalComparison F h ψ ν π lambda
    hπ hlambda τ hτ ell0 hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  obtain ⟨-, Ju, hJu0, hJu, hR⟩ := hCbound u hu
  let σu := twoBlockOppositeTwistBlocks F m τ u
  have hσu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σu i) :=
    fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).mpr (hτ i)
  let μN := unipotentQuotientHaar F.Carrier t
  let μA := unipotentQuotientHaar F.Carrier (m 0)
  let μB := unipotentQuotientHaar F.Carrier (m 1)
  have hμN := unipotentQuotientHaar_isCompatible F.Carrier t
  have hμA := unipotentQuotientHaar_isCompatible F.Carrier (m 0)
  have hμB := unipotentQuotientHaar_isCompatible F.Carrier (m 1)
  exact equalTwoBlockSymmetricGammaProduct_of_rationalComparison F h ψ ν π lambda σu
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    hπ hσu hlambda hell0 (fun i => (hσu i).1.1) Ju hJu0 hJu
    μN μA μB hμN hμA hμB (hR μN μA μB hμN hμA hμB)

end Langlands.RankinSelberg.DominantRankTransport
