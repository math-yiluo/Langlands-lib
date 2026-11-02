import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement
import Langlands.Representation.RankinSelberg.TwoBlockDominantAnalyticInputs
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockSmallLaurent
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalLaurent

/-! # The strict-dominant first-block JPSS Laurent identity -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockDominantFirstBlock

universe uF uV uW

private theorem integral_measurableSpace_transport {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (μ : @Measure X m₁) (φ : X → ℂ) :
    (letI := m₂; ∫ x, φ x ∂(hm ▸ μ)) =
      (letI := m₁; ∫ x, φ x ∂μ) := by
  cases hm
  rfl

/-- The exact closed dominant first-block identity, with the ordinary Jacquet
functional and actual convergence fixed before all measures and tests. -/
theorem twoBlockDominantFirstBlockLaurentIdentity :
    TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν t r m h htr hlt
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  intro G N GA NA NQ AQ LQ
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace GA := borel GA
  let : BorelSpace GA := ⟨rfl⟩
  let : MeasurableSpace NA := borel NA
  let : BorelSpace NA := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  let : BorelSpace LQ := ⟨rfl⟩
  intro μG μN μGA μNA μR q abv
  refine ⟨compatible_standard_quotients F t (m 0), ?_⟩
  intro V _ _ π hπ lambda W _ _ τ hτ ell
  obtain ⟨C, hC⟩ := exists_uniform_analytic_inputs F h ψ ν π hπ lambda τ hτ ell
  refine ⟨C, ?_⟩
  intro u hu σu ellu
  obtain ⟨habs, J, hJ0, hJ, hmeasures⟩ := hC u hu
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro hN hNA
  let := hN
  let := hNA
  intro νN νA hνN hνA νMinus
  obtain ⟨hsfN, hsfA, hsfMinus, hconv⟩ := hmeasures hN hNA νN νA hνN hνA
  let := hsfN
  let := hsfA
  let := hsfMinus
  refine ⟨hsfN, hsfA, hsfMinus, hconv, ?_⟩
  intro cε d hε
  obtain ⟨ζ, P, Pdual, hζ, hbody⟩ := hε
  refine ⟨ζ, P, Pdual, hζ, hbody, ?_⟩
  intro j k hr f Wtest
  subst r
  dsimp only
  obtain ⟨hP, hPd, hpairs⟩ := hbody (m 1 + 1 + j) k (firstBlockSmallRank h j k)
  have hσ : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0
      (inverseStandardCharacter ψ (m 0))).mpr
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).mp (hτ 0))
  let : ∀ n, IsTopologicalGroup (GeneralLinear n F.Carrier) :=
    T.generalLinearTopologicalGroup
  let : ∀ n, LocallyCompactSpace (GeneralLinear n F.Carrier) :=
    T.generalLinearLocallyCompactSpace
  let : ∀ n, SecondCountableTopology (GeneralLinear n F.Carrier) :=
    T.generalLinearSecondCountableTopology
  let : ∀ n, MeasurableSpace (GeneralLinear n F.Carrier) := fun _ => borel _
  let : ∀ n, BorelSpace (GeneralLinear n F.Carrier) := fun _ => ⟨rfl⟩
  let : ∀ n, MeasurableSpace (upperUnipotent n F.Carrier) := fun _ => borel _
  let : ∀ n, BorelSpace (upperUnipotent n F.Carrier) := fun _ => ⟨rfl⟩
  let : ∀ n, SecondCountableTopology (upperUnipotent n F.Carrier) :=
    fun _ => Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier
  let MQ := TwoBlockFirstBlockQuotient.MixedQuotient F h
  let LMQ := TwoBlockLowerFirstBlockQuotient.LowerMixedQuotient F h
  let MS := TwoBlockFirstBlockQuotient.mixedSubgroup F h
  let LMS := TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroup F h
  let LH := TwoBlockLowerUnipotentQuotient.lowerBlockUnipotent h F.Carrier
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace MQ := borel MQ
  let : BorelSpace MQ := ⟨rfl⟩
  let : MeasurableSpace LMQ := borel LMQ
  let : BorelSpace LMQ := ⟨rfl⟩
  let : MeasurableSpace MS := borel MS
  let : BorelSpace MS := ⟨rfl⟩
  let : MeasurableSpace LMS := borel LMS
  let : BorelSpace LMS := ⟨rfl⟩
  let : MeasurableSpace LH := borel LH
  let : BorelSpace LH := ⟨rfl⟩
  obtain ⟨νH, hνH⟩ := TwoBlockUnipotentQuotient.block_compatibleMeasureExists F.Carrier h
  obtain ⟨νM, hνM⟩ := TwoBlockFirstBlockQuotient.mixed_compatibleMeasureExists F h
  obtain ⟨νL, hνL⟩ := TwoBlockLowerFirstBlockQuotient.lowerMixed_compatibleMeasureExists F h
  have hsfH := TwoBlockLowerFirstBlockQuotient.compatibleQuotient_sigmaFinite F t H
    (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier)
    (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) νH hνH
  let := hsfH
  have hνMinus := TwoBlockLowerFirstBlockQuotient.lowerMeasure_isCompatible F h νN hνN
  have hi := firstBlock_global_laurent_identity F h j k ellu f ν.val π hπ hσ.1.1
    lambda Wtest (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val
    (fun g => hJ f g) (habs f) νN νH νA νM νL νMinus
    hνN hνH hνA hνM hνL hνMinus
    (fun a => (hconv j k rfl f Wtest).2.2 a |>.2)
    (TwoBlockFirstBlockLaurent.reflectedPolynomial q Pdual)
    (LaurentPolynomial.C ((ζ : ℂ) ^ (t + (j + k + 1)) * (cε : ℂ)) *
      LaurentPolynomial.T d * P.toLaurent)
    (fun Y g => firstBlock_small_laurent_identity F h j k ellu f ν.val π lambda
      hπ hσ Wtest νA hνA ζ cε d P Pdual hP hPd hpairs Y g)
  have hupper :
      RankinSelberg.unequalRankSliceCoefficient F j k ψ νN
        (rectangularBorelMeasure F ν.val j (t + 1)) Wtest.val
        (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val =
      (fun a => ∫ z, ∫ X, unequalRankIntegrand ψ abv j k Wtest.val
        (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val 0 X z
          ∂rectangularMeasure ν.val j (t + 1)
          ∂νN.restrict (RankinSelberg.determinantSlice T t a)) := by
    funext a
    change (∫ z, ∫ X, unequalRankIntegrand ψ abv j k Wtest.val
      (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val 0 X z
        ∂rectangularBorelMeasure F ν.val j (t + 1)
        ∂νN.restrict (RankinSelberg.determinantSlice T t a)) = _
    apply integral_congr_ae
    filter_upwards [] with z
    exact integral_measurableSpace_transport _ _ _
  erw [hupper]
  exact hi

end Langlands.RankinSelberg
