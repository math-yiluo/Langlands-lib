import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredApartmentChamber
import Langlands.BruhatTits.IntegralModels.UnramifiedFixedSubsetModels
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralZeroAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.Geometry.Building.KPZeroDatumExistence
import Langlands.Geometry.Building.UnramifiedZeroFixerSharpComparisonProof
import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof
import Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof

/-! # The arithmetic reduction for ordinary special-apartment chambers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 120000
set_option maxRecDepth 2500

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-- Connected generation over Henselian DVRs implies the unchanged ordinary
special-apartment chamber target, with no other universal premise. -/
def UnramifiedSpecialApartmentArithmeticReductionStatement : Prop :=
  ConnectedGenerationStatement.{u} → UnramifiedSpecialApartmentChamberStatement.{u}

private instance arithmeticReductionExtendedAffine {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Construct the initial fixed point, recovered models, zero datum, and torus
Iwahori model internally, retaining just the three stated arithmetic inputs. -/
theorem unramifiedSpecialApartmentChamber_of_arithmetic :
    UnramifiedTorusConnectedBoundStatement.{u} →
    UnramifiedZeroFixerSharpComparisonStatement.{u} →
    UnramifiedRootPositiveReductionStatement.{u} →
    UnramifiedSpecialApartmentChamberStatement.{u} := by
  intro hBound hSharp hpositive
  have hModel : UnramifiedTorusIwahoriModelStatement.{u} :=
    unramifiedTorusIwahoriModelAssembly IntegralModel.smoothHomExtension
      (unramifiedTorusBoundedModelAssembly maximalBoundedIntegralModel)
      hBound unramifiedTorusIwahoriConnectedImage
  intro F _ _ _ _ G hG S iS hiS T iT f hf hclosed
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C hDC hstable
  obtain ⟨p, hp⟩ := unramifiedGaloisFixedApartment F G hG T iT hiT D hstable
  have hpAffine : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisAffineAction
        F (inertiaFixedField F) iT D hstable σ p = p := by
    intro σ
    apply KPApartmentData.Apartment.ext
    exact hp σ
  let M := recoveredFixedPointModels D hG hiT C hDC p hp
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  let E := UnramifiedZeroDatum.ofConnectedReductive
    (baseChanged F (inertiaFixedField F) G)
    (hG.baseChange_of_algebraicExtension (K := inertiaFixedField F))
  have hfull : M.upper.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        B.pointwiseFixer (B.apartmentMap '' {p}) := by
    simpa only [B, MaximalUnramified.buildingDataOfApartment,
      IntegerValuationBuildingData.pointwiseFixer,
      IntegerValuationBuildingData.apartmentMap] using M.full_integralPoints
  have hN : M.upper.neutral.integralPoints =
      E.zeroPoints ⊓ D.pointwiseFixer (D.apartmentMap '' {p}) := by
    have hs := hSharp F (baseChanged F (inertiaFixedField F) G) B E {p}
      (Set.singleton_nonempty p)
      (fun g => ((Set.finite_singleton p).image g).bddAbove)
    have hn := unramifiedNeutral_integralPoints_eq_zeroFixer
      B E {p} M.upper hfull hModel hBound hs
    simpa only [B, MaximalUnramified.buildingDataOfApartment,
      IntegerValuationBuildingData.pointwiseFixer,
      IntegerValuationBuildingData.apartmentMap] using hn
  exact M.exists_regular_galois_stable_facet_of_recoveredModels
    C hDC hiS hf hG hiT E p hN hpositive hstable hpAffine

/-- Published arithmetic proofs reduce the exact chamber proposition to
connected generation over Henselian DVRs with algebraically closed residue. -/
theorem unramifiedSpecialApartmentChamber_of_connectedGeneration :
    UnramifiedSpecialApartmentArithmeticReductionStatement.{u} := by
  intro hgen
  have hLift : UnramifiedTorusNeutralSurjectivityStatement.{u} :=
    unramifiedTorusNeutralSurjectivityAssembly hgen torusQuotientRationalSurjectivity
      unramifiedTorusNeutralFiniteGeneration torusSurjectionIsogenySection
  have hBound : UnramifiedTorusConnectedBoundStatement.{u} :=
    unramifiedTorusConnectedBoundAssembly unramifiedTorusBoundedModel hLift
      unramifiedTorusNormPresentation
  exact unramifiedSpecialApartmentChamber_of_arithmetic hBound
    unramifiedZeroFixerSharpComparison unramifiedRootPositiveReduction

end Langlands.Geometry.Building
