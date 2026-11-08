import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility
import Langlands.Correspondence.AutomorphicGammaTransfer
import Langlands.Correspondence.SupercuspidalOperationRealization
import Langlands.Representation.RankinSelberg.CanonicalPairLFactor
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof
import Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonStatement
import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.Representation.RankinSelberg.SmoothDualPairFactors
import Langlands.Representation.Smooth.Contragredient.Equivalence
import Langlands.Representation.Category.UniverseLift

/-! # From class pair gamma factors to the actual generic actions -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

variable {F : PadicField.{uF} p}

local instance actualGammaFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance actualGammaValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance actualGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance actualGammaGLTopology (n : ℕ) :
    TopologicalSpace (Langlands.GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

section CharacterChange

variable {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {P : ℂ[X]}

/-- Scaling the character preserves the intrinsic polynomial, for every
compatible quotient measure. -/
theorem isPadicPairLPolynomial_characterChange (a : F.Carrierˣ) :
    IsPadicPairLPolynomial F ψ ν π σ P ↔
      IsPadicPairLPolynomial F (ψ.scale a) ν π σ P :=
  Padic.isPadicPairLPolynomial_characterChange F ψ a ν π σ P

/-- Character scaling of an intrinsic ordered pair certificate. -/
theorem IsPadicPairLPolynomial.characterChange
    (hP : IsPadicPairLPolynomial F ψ ν π σ P) (a : F.Carrierˣ) :
    IsPadicPairLPolynomial F (ψ.scale a) ν π σ P :=
  (isPadicPairLPolynomial_characterChange a).mp hP

/-- Character scaling preserves the intrinsic relation in either rank order. -/
theorem isPadicSymmetricLPolynomial_characterChange (a : F.Carrierˣ) :
    IsPadicSymmetricLPolynomial F ψ ν π σ P ↔
      IsPadicSymmetricLPolynomial F (ψ.scale a) ν π σ P :=
  Padic.isPadicSymmetricLPolynomial_characterChange F ψ a ν π σ P

/-- Character scaling of an intrinsic symmetric pair certificate. -/
theorem IsPadicSymmetricLPolynomial.characterChange
    (hP : IsPadicSymmetricLPolynomial F ψ ν π σ P) (a : F.Carrierˣ) :
    IsPadicSymmetricLPolynomial F (ψ.scale a) ν π σ P :=
  (isPadicSymmetricLPolynomial_characterChange a).mp hP

end CharacterChange

section GenericL

variable {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
  {r t : ℕ}
  {π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
  {σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}

/-- On a generic pair, every classification L-polynomial is the integral
L-polynomial of the supplied actions. -/
theorem IsLanglandsPairLPolynomial.isPadicSymmetricLPolynomial
    {P : ℂ[X]} (hP : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π σ P)
    (hπ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ r π.representation)
    (hσ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ t σ.representation) :
    IsPadicSymmetricLPolynomial F ψ ν.val π.representation σ.representation P := by
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, hall⟩ := hP
  obtain ⟨Q, hQ, hQactual⟩ :=
    genericLanglandsQuotientLFactor p F ψ ν r t d e π σ hd he hπ hσ
  exact (hQ.unique (hall d e hd he)) ▸ hQactual

end GenericL

section GenericGamma

variable {ψ : UnitaryAdditiveCharacter F.Carrier}
  {ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
  {r t : ℕ}
  {π : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
  {σ : SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}

/-- The actual smooth contragredient of a generic action is generic for the
same nontrivial additive character. -/
theorem isGeneric_contragredient (hπ : IsGeneric ψ r π.representation) :
    IsGeneric ψ r π.contragredient.representation := by
  have htype := isOfWhittakerType_smoothContragredient_inverse F π.representation ψ
    (isOfInverseWhittakerType_of_isGeneric F hπ) hπ.1
  refine ⟨?_, htype.1, htype.exists_ne_zero⟩
  exact (SmoothRep.isIrreducible_contragredient_iff
    (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData (r + 1))
    π hπ.2.1).mpr hπ.1

/-- Classification certificates on a generic pair and its actual smooth dual
give the integral gamma certificate, conditional on the epsilon comparison. -/
theorem isPadicSymmetricGammaFactor_of_langlandsFactors
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uV, uW})
    (hπ : IsGeneric ψ r π.representation) (hσ : IsGeneric ψ t σ.representation)
    {P Pd : ℂ[X]} {e : ℂˣ × ℤ}
    (hP : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π σ P)
    (hPd : IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val
      π.contragredient σ.contragredient Pd)
    (he : IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e) :
    IsPadicSymmetricGammaFactor F ψ ν.val π.representation σ.representation
      (rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P Pd) := by
  have hPdactual := hPd.isPadicSymmetricLPolynomial
    (isGeneric_contragredient hπ) (isGeneric_contragredient hσ)
  have hPdscaled := hPdactual.characterChange (-1)
  have hPdinverse :=
    (isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient
      F hπ.2.1 hσ.2.1 hπ.1 hσ.1).mpr hPdscaled
  exact (symmetricGammaExpression p F ψ ν r t π.representation σ.representation
    (genericSymmetricGammaConstructionInput F ψ ν.val ν.property
      π.representation σ.representation hπ hσ)
    e P Pd (hε p F ψ ν r t π σ hπ hσ e he)
    (hP.isPadicSymmetricLPolynomial hπ hσ) hPdinverse _).mpr rfl

end GenericGamma

end Langlands.RankinSelberg

namespace Langlands.Correspondence

open RankinSelberg HarmonicAnalysis Whittaker

universe uF uA

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance actualClassGammaFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance actualClassGammaValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance actualClassGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance actualClassGammaGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

variable {ψ : NontrivialAdditiveCharacter F}
  {ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
  {r t : ℕ}

/-- The class gamma certificate is an integral certificate on any supplied
equivalent generic saturated representatives, under the epsilon comparison. -/
theorem IsAutomorphicPairGammaFactor.isPadicSymmetricGammaFactor
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uA, uA})
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (A' : AutomorphicObject.{uF, uA} F t.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier))
    (a : J.representation.Equiv A.obj.representation)
    (a' : J'.representation.Equiv A'.obj.representation)
    (hJ : IsGeneric ψ r J.representation) (hJ' : IsGeneric ψ t J'.representation)
    {G : RationalFunctions}
    (hG : IsAutomorphicPairGammaFactor F ψ ν.val
      (automorphicClassOf F A) (automorphicClassOf F A') G) :
    IsPadicSymmetricGammaFactor F ψ ν.val J.representation J'.representation G := by
  obtain ⟨πd, πd', P, Pd, e, hd, hd', hP, hPd, he, rfl⟩ := hG
  rw [(isSmoothDual_iff_eq_contragredient F _ _).mp hd,
    (isSmoothDual_iff_eq_contragredient F _ _).mp hd'] at hPd
  have hPdJ : IsLanglandsPairLPolynomial.{uF, uA, uA} F ψ ν.val
      J.contragredient J'.contragredient Pd :=
    (isAutomorphicPairLPolynomial_iff F
      (IrreducibleAdmissibleRep.contragredient
        (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData (r + 1)) A)
      (IrreducibleAdmissibleRep.contragredient
        (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData (t + 1)) A')
      J.contragredient J'.contragredient
      (smoothContragredientEquiv a).symm (smoothContragredientEquiv a').symm).mp hPd
  exact isPadicSymmetricGammaFactor_of_langlandsFactors hε hJ hJ'
    ((isAutomorphicPairLPolynomial_iff F A A' J J' a a').mp hP) hPdJ
    ((isAutomorphicPairEpsilonFactor_iff F A A' J J' a a').mp he)

/-- Remove the saturated representative choices by the proved universe lift
and transport the gamma certificate to the original object actions. -/
theorem IsAutomorphicPairGammaFactor.isPadicSymmetricGammaFactor_of_generic
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uA, uA})
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (A' : AutomorphicObject.{uF, uA} F t.succPNat)
    (hA : IsGeneric ψ r A.obj.representation)
    (hA' : IsGeneric ψ t A'.obj.representation)
    {G : RationalFunctions}
    (hG : IsAutomorphicPairGammaFactor F ψ ν.val
      (automorphicClassOf F A) (automorphicClassOf F A') G) :
    IsPadicSymmetricGammaFactor F ψ ν.val A.obj.representation A'.obj.representation G := by
  let J := SmoothRep.universeLift.{uF} A.obj
  let J' := SmoothRep.universeLift.{uF} A'.obj
  have hJ : IsGeneric ψ r J.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r A.obj.universeLiftEquiv).mp hA
  have hJ' : IsGeneric ψ t J'.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ t A'.obj.universeLiftEquiv).mp hA'
  have hGJ := hG.isPadicSymmetricGammaFactor hε A A' J J'
    A.obj.universeLiftEquiv.symm A'.obj.universeLiftEquiv.symm hJ hJ'
  exact (IsPadicSymmetricGammaFactor.congr_equiv
    A.obj.universeLiftEquiv.symm A'.obj.universeLiftEquiv.symm).mp hGJ

/-- Class gamma certificates on generic irreducible admissible objects are
integral certificates for their original actions and the same rational function. -/
def HasGenericAutomorphicGammaComparison (F : PadicField.{uF} p) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (A' : AutomorphicObject.{uF, uA} F t.succPNat),
    (letI := F.canonicalTopologicalData.topology; IsGeneric ψ r A.obj.representation) →
    (letI := F.canonicalTopologicalData.topology; IsGeneric ψ t A'.obj.representation) →
    ∀ G : RationalFunctions,
      IsAutomorphicPairGammaFactor F ψ ν.val
        (automorphicClassOf F A) (automorphicClassOf F A') G →
      letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricGammaFactor F ψ ν.val A.obj.representation A'.obj.representation G

/-- The remaining generic epsilon comparison suffices for the class-to-actual
gamma comparison; all L-factor and smooth-dual comparisons are discharged. -/
theorem hasGenericAutomorphicGammaComparison
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uA, uA}) :
    HasGenericAutomorphicGammaComparison.{uF, uA} F := by
  intro ψ ν r t A A' hA hA' G hG
  exact hG.isPadicSymmetricGammaFactor_of_generic hε A A' hA hA'

end Langlands.Correspondence
