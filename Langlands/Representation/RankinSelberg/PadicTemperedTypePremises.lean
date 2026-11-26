import Langlands.AllField.Representation.RankinSelberg.TemperedTypePremisesStatement
import Langlands.Representation.RankinSelberg.InducedTailLFactorProof
import Langlands.Representation.RankinSelberg.AnalyticTemperedTwistLPolynomialData
import Langlands.LocalField.PadicBridge
import Langlands.Representation.Classification.TemperedLanglandsQuotientCoverageProof
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof
import Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters

/-!
# The premises of the specialized (9.4) argument over p-adic fields
-/

noncomputable section

namespace Langlands.RankinSelberg.PadicTemperedType

open Langlands.HarmonicAnalysis Langlands.Whittaker Langlands.GeneralLinear

universe uF uV uW uV₁ uV₂

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

local instance padicPremisesTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance padicPremisesValuation : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance padicPremisesLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- JPSS (9.3) over a p-adic field. -/
theorem inducedTailLFactorAt :
    AllField.RankinSelberg.InducedTailLFactorAt.{uF, uV₁, uV₂, uW} K.Carrier := by
  intro ψ ν a b t V₁ _ _ V₂ _ _ W _ _ π₁ π₂ σ h₁ h₂ hσ
  exact inducedTailLFactor.{uF, uV₁, uV₂, uW} p K ψ ν a b t π₁ π₂ σ h₁ h₂ hσ

theorem isTemperedRepresentation_iff {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n K.Carrier) V) :
    AllField.RankinSelberg.IsTemperedRepresentation ρ ↔
      K.canonicalTopologicalData.IsTempered ρ := Iff.rfl

/-- JPSS (8.4) pole bound over a p-adic field. -/
theorem temperedPoleBound :
    AllField.RankinSelberg.TemperedPoleBoundStatement.{uF, uV, uW} K.Carrier := by
  intro ψ ν r t V _ _ W _ _ τ σ hiτ htτ hiσ htσ P hP w hw
  have hP' : IsPadicSymmetricLPolynomial K ψ ν.val
      (realPowerTwist (K.canonicalTopologicalData.determinantNorm (r + 1)) 0 τ)
      (realPowerTwist (K.canonicalTopologicalData.determinantNorm (t + 1)) 0 σ) P := by
    rw [realPowerTwist_zero, realPowerTwist_zero]
    exact hP
  apply analyticTemperedTwistLPolynomial_poleFree K ψ ν τ σ hiτ htτ hiσ htσ 0 0 hP' w
  simpa using hw

/-- Irreducible tempered representations of positive rank are of Whittaker type for
every additive character. -/
theorem temperedRankWhittaker {n : ℕ} (hn : 0 < n) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ψ : UnitaryAdditiveCharacter K.Carrier)
    (ρ : Representation ℂ (GeneralLinear n K.Carrier) V)
    (hi : Representation.IsIrreducible ρ) (ht : K.canonicalTopologicalData.IsTempered ρ) :
    AllField.RankinSelberg.IsOfRankWhittakerType ψ ρ := by
  cases n with
  | zero => omega
  | succ r => exact analyticTemperedWhittakerType K ψ ρ hi ht

/-- The tempered-type datum of a genuine tempered Langlands datum over a p-adic field. -/
def temperedTypeDatumOf {n : ℕ}
    (t : K.canonicalTopologicalData.TemperedLanglandsDatum.{uV, uF} n) :
    AllField.RankinSelberg.TemperedTypeDatum.{uF, uV} (F := K.Carrier) n where
  shape := t.shape
  blocks := t.blocks
  irreducible := t.irreducible
  tempered := t.tempered
  whittaker ψ i := temperedRankWhittaker K (t.shape.positive i) ψ (t.blocks i).representation
    (t.irreducible i) (t.tempered i)
  exponent := t.exponent
  antitone := t.strictAnti.antitone

theorem temperedTypeDatumOf_standardModule {n : ℕ}
    (t : K.canonicalTopologicalData.TemperedLanglandsDatum.{uV, uF} n) :
    (temperedTypeDatumOf K t).standardModule = t.standardModule.representation := rfl

/-- The classification premise over a p-adic field: the Langlands quotient theorem
(`Classification.temperedLanglandsQuotientCoverage`) and the equality of the Whittaker
functions of a generic quotient and of its standard module. -/
theorem genericStandardModule :
    AllField.RankinSelberg.GenericStandardModuleStatement.{uF, uV} K.Carrier := by
  intro ψ r V _ _ π hπ
  let T := K.canonicalTopologicalData
  have hsmooth : IsSmooth (universeLiftRepresentation.{uF} π) :=
    (isSmooth_universeLift_iff π).mpr hπ.2.1.1
  let π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) K.Carrier) :=
    SmoothRep.of (universeLiftRepresentation.{uF} π) hsmooth
  have hirr : Representation.IsIrreducible π'.representation :=
    (isIrreducible_universeLift_iff π).mpr hπ.1
  obtain ⟨t, -, f, hf⟩ :=
    Classification.temperedLanglandsQuotientCoverage.{uF, uV} K T (r + 1) (Nat.succ_pos r) π' hirr
  let g : t.standardModule.representation.IntertwiningMap π :=
    (universeLiftEquiv.{uF} π).symm.toIntertwiningMap.comp f
  have hg : Function.Surjective g :=
    (EquivLike.surjective (universeLiftEquiv.{uF} π).symm).comp hf
  have hξ := standardModule_isOfWhittakerType_of_surjective K ψ t g hg hπ.2.2
  refine ⟨temperedTypeDatumOf K t, ?_, ?_⟩
  · exact whittakerSet_eq_of_surjective_of_whittakerType ψ hξ g hg hπ.2.2
  · exact inverseWhittakerSet_eq_of_surjective_of_whittakerType ψ
      ((isOfWhittakerType_standard_iff_inverse ψ _).mp hξ) g hg
      ((isOfWhittakerType_standard_iff_inverse ψ π).mp
        (Conductor.isOfWhittakerType_of_isGeneric_localField hπ)).exists_ne_zero

end Langlands.RankinSelberg.PadicTemperedType
