import Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeStatement
import Langlands.Geometry.Building.UnramifiedRootRadicalPositivity
import Langlands.BruhatTits.IntegralModels.UnramifiedRootIntegrality
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorus
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsStatement
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Depth-zero opposite factors from recovered nearby parabolic models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

private instance recoveredOppositeExtendedAffine {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

private instance recoveredOppositeExtendedSmooth {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [Smooth G.X.hom] :
    Smooth (baseChanged F (inertiaFixedField F) G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- The remaining recovered-model availability used by the depth-zero
argument: full singleton fixer recovery and nearby parabolic root comparisons.
No positive-depth-to-radical implication is required. -/
def UnramifiedFixedRecoveredParabolicModelsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    haveI := mono_of_isMaximalSplitTorus hiS
    ∀ (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI : Mono ((GroupScheme.baseChange
        (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
          mono_of_isMaximalSplitTorus hiT
      ∀ (hE : RelativeRoot.HasOppositeFactorPairs
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        ∀ z : D.Apartment,
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ z.val = z.val) →
          ∃ (L : RelativeComponentModelData ↥𝒪[F] F G)
            (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
              (baseChanged F (inertiaFixedField F) G))
            (_e : UnramifiedComponentModelRecovery L E),
            E.full.integralPoints =
              characterValuationKernel (MaximalUnramified.valuation F)
                  (baseChanged F (inertiaFixedField F) G) ⊓
                D.pointwiseFixer (D.apartmentMap '' ({z} : Set D.Apartment)) ∧
            D.ParabolicRootComparisonsNearDescentTranslations f
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE iS L z

/-- Recovered models with nearby parabolic root comparisons, together with
the integral opposite-factor theorem, imply the unchanged exact target. -/
def UnramifiedRecoveredDepthZeroOppositeReductionStatement : Prop :=
  UnramifiedFixedRecoveredParabolicModelsStatement.{u} →
    IntegralOppositeFactorsStatement.{u} →
      UnramifiedFixedDepthZeroOppositeStatement.{u}

set_option maxHeartbeats 8000000 in
/-- Construct the closed integral torus and actual reductive quotient, exclude
value-zero root points from the radical, and apply integral opposite factors. -/
theorem unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels :
    UnramifiedRecoveredDepthZeroOppositeReductionStatement.{u} := by
  intro hmodels hop F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
      mono_of_isMaximalSplitTorus hiT
  intro hE D C hDC fixed φ z hz a ha g hg hg1 hzero g' hg' g'' hg'' hm
  obtain ⟨L, E, e, hfull, hnear⟩ :=
    hmodels F G hG S iS hiS T iT f hf hiT hE D C hDC z hz
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    hG.baseChange_of_algebraicExtension
  obtain ⟨A, hA⟩ := exists_closedSplitIntegralTorus_of_fullRecovery D C
    hiS hf hDC L E e ({z} : Set D.Apartment) hfull
  obtain ⟨Q, hQ⟩ := SpecialFibreQuotientData.exists_isReductiveQuotient L
  have hgint : g ∈ L.neutral.integralPoints :=
    mem_neutral_integralPoints_of_nonnegative_restrictedDepth L E e hGK hiT
      D C hDC f hf hiS.isSplitSubtorus.1 hE z hfull ha hg hzero.symm.le
  have hgnpos : g ∉ Q.positivePoints :=
    D.not_mem_positivePoints_of_eq_zero_of_parabolicRootComparisons
      f hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
      hnear Q hQ.1 ha hg hzero
  have hints : g' ∈ L.neutral.integralPoints ∧ g'' ∈ L.neutral.integralPoints :=
    (hop F G hG S iS hiS L A Q hA hQ a ha g hg hg1 hgint
      g' hg' g'' hg'' hm).mpr hgnpos
  have hna : -a ∈ relativeRoots iS :=
    relativeRootNegation F G hG S iS hiS a ha
  exact ⟨nonnegative_restrictedDepth_of_mem_neutral_integralPoints L E e hGK hiT
      D f hf hiS.isSplitSubtorus.1 hE z hfull hna hg' hints.1,
    nonnegative_restrictedDepth_of_mem_neutral_integralPoints L E e hGK hiT
      D f hf hiS.isSplitSubtorus.1 hE z hfull hna hg'' hints.2⟩

end Langlands.Geometry.Building
