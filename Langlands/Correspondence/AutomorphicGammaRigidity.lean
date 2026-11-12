import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Correspondence.AutomorphicGammaTransfer
import Langlands.Representation.RankinSelberg.BlockShapeSmoothDualGamma
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityProof

/-! # Actual unitary supercuspidal products from self-pair gamma rigidity -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker Classification LocalFactor

universe uF uA uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

/-- Exhaustion and the existing actual segment parametrization remove the
block and segment choices from the whole smooth-dual gamma rigidity theorem. -/
theorem unitarySupercuspidalProduct_of_generic_smoothDualGamma
    (hEx : UnitaryGenericExhaustion.{uF, uA} F F.canonicalTopologicalData)
    (hH : SegmentHeadLFactorStatement.{uF, max uF uA, max uF uA})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uA, max uF uA})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r : ℕ}
    (π : SmoothRep.{0, uF, uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (hπ : IsGeneric ψ r π.representation)
    (hu : IsUnitarizable π.representation)
    {G : RatFunc ℂ}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val
      π.representation (smoothContragredient π.representation) G)
    (hzero : ∀ t : ℝ, 0 < meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
      t = 0) :
    ∃ B : BlockShape (r + 1),
      IsUnitarySupercuspidalProduct.{uF, uW, uA}
        F F.canonicalTopologicalData B π.representation := by
  let J := SmoothRep.universeLift.{uF} π
  have hJ : IsGeneric ψ r J.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r π.universeLiftEquiv).mp hπ
  have huJ : IsUnitarizable J.representation :=
    (isUnitarizable_iff_of_equiv π.universeLiftEquiv).mp hu
  obtain ⟨B, δ, s, hU, ⟨e⟩⟩ := hEx r ψ J hJ huJ
  let d := hU.1.segmentParameters F F.canonicalTopologicalData
  exact ⟨B, unitarySupercuspidalProduct_of_smoothDualGamma F ψ ν hH hEq
    B δ s d hU π.representation
    (π.universeLiftEquiv.trans (SmoothRep.equivOfIso e)) hπ.2.2 hG hzero⟩

end Langlands.RankinSelberg

namespace Langlands.Correspondence

open GeneralLinear HarmonicAnalysis Whittaker Classification RankinSelberg LocalFactor

universe uF uA uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance instTopologicalSpaceCarrier_automorphicGammaRigidity :
    TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

/-- A class smooth-dual relation identifies a supplied representative with the
actual whole smooth dual, and supplies its genericity by actual equivalences. -/
theorem IsAutomorphicPairGammaFactor.isPadicSymmetricGammaFactor_selfPair
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uA, uA})
    {ψ : NontrivialAdditiveCharacter F}
    {ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
    {r : ℕ}
    (A A' : AutomorphicObject.{uF, uA} F r.succPNat)
    (hd : IsSmoothDual F (automorphicClassOf F A) (automorphicClassOf F A'))
    (hA : IsGeneric ψ r A.obj.representation)
    {G : RatFunc ℂ}
    (hG : IsAutomorphicPairGammaFactor F ψ ν.val
      (automorphicClassOf F A) (automorphicClassOf F A') G) :
    IsPadicSymmetricGammaFactor F ψ ν.val
      A.obj.representation (smoothContragredient A.obj.representation) G := by
  let Ad : AutomorphicObject.{uF, uA} F r.succPNat :=
    IrreducibleAdmissibleRep.contragredient
      (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData r.succPNat) A
  have hclass : automorphicClassOf F Ad = automorphicClassOf F A' :=
    ((isSmoothDual_iff_eq_contragredient F _ _).mp hd).symm
  obtain ⟨e⟩ := (automorphicClassOf_eq_iff F Ad A').mp hclass
  let J := SmoothRep.universeLift.{uF} A.obj
  have hJ : IsGeneric ψ r J.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r A.obj.universeLiftEquiv).mp hA
  have hAd : IsGeneric ψ r Ad.obj.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r
      (smoothContragredientEquiv A.obj.universeLiftEquiv)).mp
        (RankinSelberg.isGeneric_contragredient hJ)
  have hA' : IsGeneric ψ r A'.obj.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r e).mp hAd
  have hactual := hG.isPadicSymmetricGammaFactor_of_generic hε A A' hA hA'
  exact (IsPadicSymmetricGammaFactor.congr_equiv
    (equivOfRepresentationEq (rfl : A.obj.representation = A.obj.representation))
    e.symm).mp hactual

/-- Class self-pair gamma data with positive real order only at zero force a
unitary supercuspidal product on the original generic unitarizable action. -/
theorem unitarySupercuspidalProduct_of_classSelfPairGamma
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uA, uA})
    (hEx : UnitaryGenericExhaustion.{uF, uA} F F.canonicalTopologicalData)
    (hH : SegmentHeadLFactorStatement.{uF, max uF uA, max uF uA})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uA, max uF uA})
    {ψ : NontrivialAdditiveCharacter F}
    {ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
    {r : ℕ}
    (A A' : AutomorphicObject.{uF, uA} F r.succPNat)
    (hd : IsSmoothDual F (automorphicClassOf F A) (automorphicClassOf F A'))
    (hA : IsGeneric ψ r A.obj.representation)
    (hu : IsUnitarizable A.obj.representation)
    {G : RatFunc ℂ}
    (hG : IsAutomorphicPairGammaFactor F ψ ν.val
      (automorphicClassOf F A) (automorphicClassOf F A') G)
    (hzero : ∀ t : ℝ, 0 < meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
      t = 0) :
    ∃ B : BlockShape (r + 1),
      IsUnitarySupercuspidalProduct.{uF, uW, uA}
        F F.canonicalTopologicalData B A.obj.representation :=
  unitarySupercuspidalProduct_of_generic_smoothDualGamma F hEx hH hEq ψ ν A.obj hA hu
    (hG.isPadicSymmetricGammaFactor_selfPair hε A A' hd hA) hzero

/-- The local rigidity conclusion for every generic unitarizable original
object and supplied class smooth dual with a certified self-pair gamma factor. -/
def HasUnitarySupercuspidalProductOfClassSelfPairGamma (F : PadicField.{uF} p) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r : ℕ) (A A' : AutomorphicObject.{uF, uA} F r.succPNat),
    IsSmoothDual F (automorphicClassOf F A) (automorphicClassOf F A') →
    IsGeneric ψ r A.obj.representation →
    IsUnitarizable A.obj.representation →
    ∀ G : RatFunc ℂ,
      IsAutomorphicPairGammaFactor F ψ ν.val
        (automorphicClassOf F A) (automorphicClassOf F A') G →
      (∀ t : ℝ, 0 < meromorphicOrderAt
        (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
        t = 0) →
      ∃ B : BlockShape (r + 1),
        IsUnitarySupercuspidalProduct.{uF, uW, uA}
          F F.canonicalTopologicalData B A.obj.representation

/-- All block and segment choices and representative transports are discharged;
the exact epsilon, exhaustion and factor-formula prerequisites remain explicit. -/
theorem hasUnitarySupercuspidalProductOfClassSelfPairGamma
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uA, uA})
    (hEx : UnitaryGenericExhaustion.{uF, uA} F F.canonicalTopologicalData)
    (hH : SegmentHeadLFactorStatement.{uF, max uF uA, max uF uA})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uA, max uF uA}) :
    HasUnitarySupercuspidalProductOfClassSelfPairGamma.{uF, uA, uW} F := by
  intro ψ ν r A A' hd hA hu G hG hzero
  exact unitarySupercuspidalProduct_of_classSelfPairGamma hε hEx hH hEq
    A A' hd hA hu hG hzero

end Langlands.Correspondence

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE uW uQ

open Langlands.Global Langlands.Global.CompletionPadic
open Correspondence RankinSelberg Classification LocalFactor LocalFactor.CommonClosure Whittaker

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- An actual unitary relative Weil self-pair match supplies the self-dual
measure, a certified class gamma factor and its positive-order restriction. -/
theorem unitarySupercuspidalProduct_of_localSelfPairMatch
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{u, u, u})
    (hEx : UnitaryGenericExhaustion.{u, u} (padicField v)
      (padicField v).canonicalTopologicalData)
    (hH : SegmentHeadLFactorStatement.{u, u, u})
    (hEq : SupercuspidalEqualRankLFactorStatement.{u, u, u})
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uE} (padicField v)}
    {hεs : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : NontrivialAdditiveCharacter (padicField v)} {r : ℕ}
    (A A' : AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (hd : IsSmoothDual (padicField v) (automorphicClassOf _ A) (automorphicClassOf _ A'))
    (hA : letI := (padicField v).canonicalTopologicalData.topology
      IsGeneric ψ r A.obj.representation)
    (hu : letI := (padicField v).canonicalTopologicalData.topology
      IsUnitarizable A.obj.representation)
    (hmatch : IsPairGammaMatch (padicField v) eC ε hεs ψ
      (automorphicClassOf _ A) (automorphicClassOf _ A')
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι)) :
    letI := (padicField v).canonicalTopologicalData.topology
    ∃ B : GeneralLinear.BlockShape (r + 1),
      IsUnitarySupercuspidalProduct.{u, uW, u} (padicField v)
        (padicField v).canonicalTopologicalData B A.obj.representation := by
  obtain ⟨ν, hν⟩ := hmatch.1
  obtain ⟨G, hG, -⟩ := hmatch.2 ν hν
  exact unitarySupercuspidalProduct_of_classSelfPairGamma (ν := ⟨ν, hν⟩) hε hEx hH hEq
    A A' hd hA hu hG
    (localSelfPair_rationalSpectralValue_real_positive_order_only_zero ι hS hmatch hν hG)

/-- At a finite place, the proved local genericity and unitarity of a cuspidal
component with unitary central character discharge the representation-side
premises; the conclusion is the body of the host induction statement. -/
theorem localComponent_unitarySupercuspidalProduct_of_selfPairMatch
    [CompactSpace (AdeleQuotient F)]
    (hε : GenericLanglandsPairEpsilonFactorComparisonStatement.{u, u, u})
    (hEx : UnitaryGenericExhaustion.{u, u} (padicField v)
      (padicField v).canonicalTopologicalData)
    (hH : SegmentHeadLFactorStatement.{u, u, u})
    (hEq : SupercuspidalEqualRankLFactorStatement.{u, u, u})
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uE} (padicField v)}
    {hεs : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : NontrivialAdditiveCharacter (padicField v)} {r : ℕ}
    {T : Automorphic.CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (A' : AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (hd : IsSmoothDual (padicField v) ((P.localComponent v).padicClass hI hA)
      (automorphicClassOf _ A'))
    (hmatch : IsPairGammaMatch (padicField v) eC ε hεs ψ
      ((P.localComponent v).padicClass hI hA) (automorphicClassOf _ A')
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι)) :
    letI := (padicField v).canonicalTopologicalData.topology
    ∃ (B : GeneralLinear.BlockShape (r + 1))
      (σ : ∀ i, GeneralLinear.SupercuspidalRep.{u, u}
        (F := (padicField v).Carrier) (n := B.size i)),
      (∀ i, IsUnitarizable (σ i).obj.representation) ∧
        Nonempty (((P.localComponent v).padicObject hI hA).obj.representation.Equiv
          ((padicField v).canonicalTopologicalData.normalizedProductInduced B
            fun i => (σ i).obj.representation)) :=
  unitarySupercuspidalProduct_of_localSelfPairMatch.{u, uV, uE, u} hε hEx hH hEq ι hS
    ((P.localComponent v).padicObject hI hA) A' hd
    (Automorphic.cuspidalUnitaryLocalGenericity F r T hT P v hI hA ψ)
    (Automorphic.cuspidalUnitaryLocalUnitarity F r T hT P v hI hA) hmatch

end Langlands.ClassField.Global.RelativeWeilGroup
