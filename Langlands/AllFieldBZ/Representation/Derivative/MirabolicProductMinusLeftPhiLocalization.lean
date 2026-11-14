import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility leftPhiAmbientSectionCharacter leftPhiCharacter_rankCast_symm leftPhiExpected leftPhiExpectedHostIso leftPhiExpectedPullback leftPhiHigherSectionMap leftPhiHigherSectionRepresentation leftPhiHostCompactInducedEquiv leftPhiHostCompactInducedEquiv_eval leftPhiHostCompactInducedEquiv_natural leftPhiHostInducingFunctor leftPhiHostInducingMap leftPhiHostInducingRepresentation leftPhiHostInducingRepresentation_smooth leftPhiHostInductionIso leftPhiMackeyInjection leftPhiMackeyInput leftPhiMackeyLocalizedCycle_subsingleton leftPhiMackeyLocalizedIso leftPhiMackeyLocalizedProjection leftPhiMackeyLocalizedProjection_bijective leftPhiMackeyProjection leftPhiMackey_exact leftPhiMackey_exists_exact leftPhiNormalizedIdentityPiece leftPhiNormalizedRadicalEquiv leftPhiNormalizedRadicalEquiv_mk leftPhiNormalizedSection_scalar leftPhiNormalizedSourceEquiv leftPhiNormalizedSourceEquiv_mk_tmul leftPhiNormalizedSourceEquiv_natural leftPhiNormalizedSource_action_tmul leftPhiNormalizedStabilizer leftPhiNormalizedStabilizerMap leftPhiNormalizedStabilizer_radical leftPhiNormalizedStagesAction leftPhiNormalizedStagesCoefficientEquiv leftPhiNormalizedStagesCoefficientEquiv_action_mk leftPhiNormalizedStagesCoefficientEquiv_mk leftPhiNormalizedStagesCoefficientEquiv_natural leftPhiNormalizedStagesCoefficientEquiv_one_tmul leftPhiNormalizedStagesMap leftPhiNormalizedStagesMap_mk leftPhiNormalizedStagesQuotient leftPhiNormalizedStagesQuotient_zero_subsingleton leftPhiNormalizedStagesTensorEquiv leftPhiNormalizedStagesTensorEquiv_action_tmul leftPhiNormalizedStagesTensorEquiv_mk_tmul leftPhiNormalizedStagesTensorEquiv_natural leftPhiPlusKernelFunctor leftPhiProduct leftPhiProductIdentityIso leftPhiSectionCharacter leftPhiSectionCharacter_apply leftPhiSectionCharacter_eq leftPhiSourceCoefficient leftPhiSourceCoefficientMap leftPhiSourceCoefficient_tmul_quotient leftPhiSourceQuotient leftPhiSourceQuotient_factor leftPhiSourceQuotient_naturality leftPhiSourceQuotient_surjective leftPhiSourceQuotient_tmul leftPhiStabilizerCharacter leftPhiStabilizerCharacter_radical leftPhiSubgroup_determinantNorm leftPhiTransportedSourceCoefficient leftPhiTransportedSourceMap mirabolicRankCastMixedOrbitIso padic_leftPhiStagesCharacterEquiv padic_leftPhiStagesCharacterEquiv_natural phiMinusKernelAction phiMinusKernelAction_smooth phiMinusKernelEquiv phiMinusKernelEquiv_mk phiMinusKernelEquiv_natural phiMinusKernelFunctor phiMinusKernelIso phiMinusKernelMap phiMinusNormalizedKernelEquiv phiMinusNormalizedKernelEquiv_mk phiMinusNormalizedKernelIso plusKernelSmoothTheta rightPhiProduct rightPhiQuotient rightPhiSubobject
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding MirabolicMixedOrbitCoverageStatement isTopologicalRing_of_topologicalData mirabolicMixedOrbitCoverage
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.Induction
open Langlands.Geometric
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)

/-- The full identity-orbit quotient with the actual ambient inverse-half
determinant normalization, naturally in both original smooth inputs. -/
def leftPhiNormalizedIdentityPiece :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      Rep.{max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  (leftPhiMackeyInput T k r ⋙
    orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
      (leftRepresentative k r F.Carrier 1) ⋙ leftPhiPlusKernelFunctor T k r ψ) ⋙
    (⟨Mirabolic.phiMinusCharacter T (k + r + 1),
      Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩ :
        SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier)).twistFunctor

private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiProductAssociationIso :
    letI := T.topology
    leftPhiProduct.{uF, uV} T ψ k (r + 1) ≅
      (T.leftMixedProductFunctor (k + 1) (r + 1) ⋙
        mirabolicRankCast T (totalRank_eq k r)) ⋙
          Mirabolic.phiMinus T ψ (k + r + 1) :=
  letI := T.topology
  (Functor.associator (T.leftMixedProductFunctor (k + 1) (r + 1))
    (mirabolicRankCast T (totalRank_eq k r))
    (Mirabolic.phiMinus T ψ (k + r + 1))).symm

set_option maxHeartbeats 800000 in
/-- Actual Phi-minus of the higher mixed product is the normalized full
identity-orbit localization. The map uses the published natural Mackey quotient. -/
def leftPhiProductIdentityIso :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    leftPhiProduct.{uF, uV} T ψ k (r + 1) ⋙ SmoothRep.toRep ≅
      leftPhiNormalizedIdentityPiece T ψ k r := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  let χ : SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier) :=
    ⟨Mirabolic.phiMinusCharacter T (k + r + 1),
      Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩
  let H := leftPhiMackeyInput.{uF, uV} T k r ⋙ SmoothRep.toRep ⋙
    compactInductionFunctor (leftInducing k r F.Carrier)
  let e₁ :
      ((T.leftMixedProductFunctor (k + 1) (r + 1) ⋙
        mirabolicRankCast T (totalRank_eq k r)) ⋙
          (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep)) ≅
        H ⋙ (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep) :=
    Functor.isoWhiskerRight (leftPhiHostInductionIso.{uF, uV} T k r)
      (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep)
  let e₂ : H ⋙ (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep) ≅
      (leftPhiMackeyInput T k r ⋙
        restrictedCompactInduction (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) ⋙ leftPhiPlusKernelFunctor T k r ψ) ⋙
        χ.twistFunctor :=
    Functor.isoWhiskerLeft H
      (Functor.isoWhiskerRight (phiMinusNormalizedKernelIso T ψ (k + r + 1)).symm
        SmoothRep.toRep)
  let e₃ := Functor.isoWhiskerRight
    (leftPhiMackeyLocalizedIso.{uF, uV} T k r ψ) χ.twistFunctor
  let e₀ := Functor.isoWhiskerRight (leftPhiProductAssociationIso.{uF, uV} T ψ k r)
    SmoothRep.toRep
  let a := Functor.associator
    (T.leftMixedProductFunctor (k + 1) (r + 1) ⋙ mirabolicRankCast T (totalRank_eq k r))
    (Mirabolic.phiMinus T ψ (k + r + 1)) SmoothRep.toRep
  let e := e₀ ≪≫ a ≪≫ e₁ ≪≫ e₂ ≪≫ e₃
  unfold leftPhiNormalizedIdentityPiece
  with_reducible exact e

end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
