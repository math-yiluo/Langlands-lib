import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility leftPhiAmbientInductionEquiv leftPhiAmbientInductionEquiv_eval leftPhiAmbientInductionEquiv_natural leftPhiAmbientSectionCharacter leftPhiCharacter_rankCast_symm leftPhiCompactSourceEquiv leftPhiCompactSourceEquiv_eval leftPhiCompactSourceEquiv_natural leftPhiCompatibility leftPhiCompatibilityIso leftPhiExpected leftPhiExpectedHostIso leftPhiExpectedPullback leftPhiHigherSectionMap leftPhiHigherSectionRepresentation leftPhiHostCompactInducedEquiv leftPhiHostCompactInducedEquiv_eval leftPhiHostCompactInducedEquiv_natural leftPhiHostInducingFunctor leftPhiHostInducingMap leftPhiHostInducingRepresentation leftPhiHostInducingRepresentation_smooth leftPhiHostInductionIso leftPhiIdentityNormalizedEquiv leftPhiIdentityNormalizedEquiv_natural leftPhiMackeyInjection leftPhiMackeyInput leftPhiMackeyLocalizedCycle_subsingleton leftPhiMackeyLocalizedIso leftPhiMackeyLocalizedProjection leftPhiMackeyLocalizedProjection_bijective leftPhiMackeyProjection leftPhiMackey_exact leftPhiMackey_exists_exact leftPhiNormalizedIdentityPiece leftPhiNormalizedRadicalEquiv leftPhiNormalizedRadicalEquiv_mk leftPhiNormalizedSection_scalar leftPhiNormalizedSourceEquiv leftPhiNormalizedSourceEquiv_mk_tmul leftPhiNormalizedSourceEquiv_natural leftPhiNormalizedSourceEquiv_rank_action leftPhiNormalizedSource_action_tmul leftPhiNormalizedStabilizer leftPhiNormalizedStabilizerMap leftPhiNormalizedStabilizer_radical leftPhiNormalizedStabilizer_smooth leftPhiNormalizedStagesAction leftPhiNormalizedStagesCoefficientEquiv leftPhiNormalizedStagesCoefficientEquiv_action_mk leftPhiNormalizedStagesCoefficientEquiv_mk leftPhiNormalizedStagesCoefficientEquiv_natural leftPhiNormalizedStagesCoefficientEquiv_one_tmul leftPhiNormalizedStagesMap leftPhiNormalizedStagesMap_mk leftPhiNormalizedStagesQuotient leftPhiNormalizedStagesQuotient_zero_subsingleton leftPhiNormalizedStagesTensorEquiv leftPhiNormalizedStagesTensorEquiv_action_tmul leftPhiNormalizedStagesTensorEquiv_mk_tmul leftPhiNormalizedStagesTensorEquiv_natural leftPhiPlusKernelFunctor leftPhiProduct leftPhiProductIdentityIso leftPhiSectionCharacter leftPhiSectionCharacter_apply leftPhiSectionCharacter_eq leftPhiSourceCoefficient leftPhiSourceCoefficientMap leftPhiSourceCoefficient_tmul_quotient leftPhiSourceQuotient leftPhiSourceQuotient_factor leftPhiSourceQuotient_naturality leftPhiSourceQuotient_surjective leftPhiSourceQuotient_tmul leftPhiStabilizerCharacter leftPhiStabilizerCharacter_radical leftPhiSubgroup_determinantNorm leftPhiTransportedSourceCoefficient leftPhiTransportedSourceMap mirabolicRankCastMixedOrbitIso padic_leftPhiStagesCharacterEquiv padic_leftPhiStagesCharacterEquiv_natural phiMinusKernelAction phiMinusKernelAction_smooth phiMinusKernelEquiv phiMinusKernelEquiv_mk phiMinusKernelEquiv_natural phiMinusKernelFunctor phiMinusKernelIso phiMinusKernelMap phiMinusNormalizedKernelEquiv phiMinusNormalizedKernelEquiv_mk phiMinusNormalizedKernelIso plusKernelSmoothTheta rightPhiProduct rightPhiQuotient rightPhiSubobject
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding MirabolicMixedOrbitCoverageStatement isTopologicalRing_of_topologicalData mirabolicMixedOrbitCoverage
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.Induction
open Langlands.Geometric
open Langlands.Induction.SplitKernelLocalization
open Langlands.MixedProductTensor
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)

private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerFunctor (i : Fin 2) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      Rep.{uV} ℂ (leftStabilizer k r F.Carrier i) :=
  letI := T.topology
  { obj X := Rep.of (leftPhiNormalizedStabilizer T k r X.1.representation X.2.representation i)
    map f := Rep.ofHom (leftPhiNormalizedStabilizerMap T k r _ _
      (SmoothRep.hom f.1) (SmoothRep.hom f.2) i)
    map_id X := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change TensorProduct.map LinearMap.id LinearMap.id x = x
      rw [TensorProduct.map_id]
      rfl
    map_comp f g := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun
        (congrArg Representation.IntertwiningMap.toLinearMap
          (externalMap_comp (SmoothRep.hom f.1) (SmoothRep.hom g.1)
            (SmoothRep.hom f.2) (SmoothRep.hom g.2))) x }

set_option maxHeartbeats 800000 in
private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerRestrictionIso (i : Fin 2) :
    letI := T.topology
    leftPhiMackeyInput.{uF,uV} T k r ⋙ SmoothRep.toRep ⋙
      Rep.resFunctor (stabilizerToInducing (leftInducing k r F.Carrier)
        (plusSubgroup (k + r + 1) F.Carrier) (leftRepresentative k r F.Carrier i)) ≅
      leftPhiStabilizerFunctor T k r i := by
  letI := T.topology
  refine NatIso.ofComponents (fun X => Rep.mkIso
    { toLinearEquiv := LinearEquiv.refl ℂ _
      isIntertwining' g := ?_ }) ?_
  · rfl
  · intro X Y f
    rfl

private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerLocalizedFunctor :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      Rep.{max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  leftPhiStabilizerFunctor T k r 1 ⋙
    compactInductionFunctor (leftStabilizer k r F.Carrier 1) ⋙
      SmoothRep.toRep ⋙ leftPhiPlusKernelFunctor T k r ψ ⋙
        (⟨Mirabolic.phiMinusCharacter T (k + r + 1),
          Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩ :
            SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier)).twistFunctor

set_option maxHeartbeats 800000 in
private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerLocalizationIso :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    (leftPhiMackeyInput.{uF,uV} T k r ⋙
      orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
        (leftRepresentative k r F.Carrier 1) ⋙ leftPhiPlusKernelFunctor T k r ψ) ⋙
      (⟨Mirabolic.phiMinusCharacter T (k + r + 1),
        Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩ :
          SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier)).twistFunctor ≅
      leftPhiStabilizerLocalizedFunctor T ψ k r := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  let χ : SmoothCharacter ℂ (mirabolic (k + r + 1) F.Carrier) :=
    ⟨Mirabolic.phiMinusCharacter T (k + r + 1),
      Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩
  let M := leftPhiMackeyInput.{uF,uV} T k r
  let U := SmoothRep.toRep (R := ℂ) (G := leftInducing k r F.Carrier)
  let R := Rep.resFunctor (k := ℂ)
    (stabilizerToInducing (leftInducing k r F.Carrier)
      (plusSubgroup (k + r + 1) F.Carrier) (leftRepresentative k r F.Carrier 1))
  let C := compactInductionFunctor (leftStabilizer k r F.Carrier 1) (R := ℂ)
  let V := SmoothRep.toRep (R := ℂ) (G := plusSubgroup (k + r + 1) F.Carrier)
  let K := leftPhiPlusKernelFunctor T k r ψ
  let O := orbitPiece (leftInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier)
    (leftRepresentative k r F.Carrier 1) (R := ℂ)
  let a₀ := Functor.associator M (O ⋙ K) χ.twistFunctor
  let a₁ := Functor.isoWhiskerLeft M (Functor.associator O K χ.twistFunctor)
  let a₂ : O ⋙ K ⋙ χ.twistFunctor ≅ U ⋙ R ⋙ C ⋙ V ⋙ K ⋙ χ.twistFunctor :=
    Functor.associator U (R ⋙ C ⋙ V) (K ⋙ χ.twistFunctor) ≪≫
      Functor.isoWhiskerLeft U
        (Functor.associator R (C ⋙ V) (K ⋙ χ.twistFunctor) ≪≫
          Functor.isoWhiskerLeft R (Functor.associator C V (K ⋙ χ.twistFunctor)))
  let a₃ := (Functor.associator M (U ⋙ R) (C ⋙ V ⋙ K ⋙ χ.twistFunctor)).symm
  let e := Functor.isoWhiskerRight (leftPhiStabilizerRestrictionIso.{uF,uV} T k r 1)
    (C ⋙ V ⋙ K ⋙ χ.twistFunctor)
  exact a₀ ≪≫ a₁ ≪≫ Functor.isoWhiskerLeft M a₂ ≪≫ a₃ ≪≫ e

private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiSourceFunctor :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      Rep.{uV} ℂ (leftSubgroup (k + 1) r F.Carrier) :=
  letI := T.topology
  { obj X := Rep.of (leftPhiSourceCoefficient T k r ψ X.1.representation X.2)
    map f := Rep.ofHom (leftPhiSourceCoefficientMap T k r ψ _ _
      (SmoothRep.hom f.1) (SmoothRep.hom f.2))
    map_id X := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      change TensorProduct.map LinearMap.id
        (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map (𝟙 X.2))).toLinearMap = LinearMap.id
      rw [(Mirabolic.phiMinus T ψ r).map_id]
      exact TensorProduct.map_id
    map_comp f g := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      change TensorProduct.map
          ((SmoothRep.hom g.1).toLinearMap.comp (SmoothRep.hom f.1).toLinearMap)
          (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map (f.2 ≫ g.2))).toLinearMap = _
      rw [(Mirabolic.phiMinus T ψ r).map_comp]
      exact congrArg Representation.IntertwiningMap.toLinearMap
        (externalMap_comp (SmoothRep.hom f.1) (SmoothRep.hom g.1)
          (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map f.2))
          (SmoothRep.hom ((Mirabolic.phiMinus T ψ r).map g.2))) }

private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiSourceInducedFunctor :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      Rep.{max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  leftPhiSourceFunctor T ψ k r ⋙
    compactInductionFunctor (leftSubgroup (k + 1) r F.Carrier) ⋙
      SmoothRep.toRep ⋙ Rep.resFunctor (leftPhiLowerRankEquiv k r F.Carrier).toMonoidHom

set_option maxHeartbeats 4000000 in
/-- The object component, elaborated in its own declaration. -/
private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerSourceIsoApp
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    (leftPhiStabilizerLocalizedFunctor.{uF,uV} T ψ k r).obj X ≅
      (leftPhiSourceInducedFunctor T ψ k r).obj X := by
  letI := T.topology
  letI := T.fieldT2
  letI := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  letI := T.generalLinearTopologicalGroup (k + r + 2)
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  dsimp only [leftPhiStabilizerLocalizedFunctor, leftPhiStabilizerFunctor,
    leftPhiSourceInducedFunctor, leftPhiSourceFunctor, Functor.comp_obj,
    compactInductionFunctor, SmoothRep.toRep, leftPhiPlusKernelFunctor,
    SmoothCharacter.twistFunctor, ObjectProperty.ι, inducedFunctor, Rep.resFunctor]
  refine Rep.mkIso ?_
  let e := leftPhiIdentityNormalizedEquiv T k r X.1.representation ψ X.2 X.1.isSmooth
  dsimp only [Rep.of, SmoothRep.representation] at e ⊢
  with_reducible exact e

set_option maxHeartbeats 4000000 in
/-- Naturality of the object components, elaborated in its own declaration. -/
private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerSourceIsoApp_natural
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)} (f : X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    (leftPhiStabilizerLocalizedFunctor.{uF,uV} T ψ k r).map f ≫
        (leftPhiStabilizerSourceIsoApp T ψ k r Y).hom =
      (leftPhiStabilizerSourceIsoApp T ψ k r X).hom ≫
        (leftPhiSourceInducedFunctor T ψ k r).map f := by
  let := T.topology
  let := T.fieldT2
  let := Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit.isTopologicalRing_of_topologicalData F T
  let := T.generalLinearTopologicalGroup (k + r + 3)
  let := T.generalLinearTopologicalGroup (k + r + 2)
  let := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  exact leftPhiIdentityNormalizedEquiv_natural T k r X.1.representation ψ X.2
    X.1.isSmooth Y.1.isSmooth (SmoothRep.hom f.1) (SmoothRep.hom f.2) z

private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerSourceIso :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 3)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    leftPhiStabilizerLocalizedFunctor.{uF,uV} T ψ k r ≅
      leftPhiSourceInducedFunctor T ψ k r :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  NatIso.ofComponents (leftPhiStabilizerSourceIsoApp T ψ k r)
    (leftPhiStabilizerSourceIsoApp_natural T ψ k r)

set_option maxHeartbeats 800000 in
private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiSourceExpectedIsoApp
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    (leftPhiSourceInducedFunctor.{uF,uV} T ψ k r).obj X ≅
      (leftPhiExpectedPullback T k r ψ ⋙ SmoothRep.toRep).obj X := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  exact Iso.refl _

set_option maxHeartbeats 800000 in
private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiSourceExpectedIsoApp_natural
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)} (f : X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    (leftPhiSourceInducedFunctor.{uF,uV} T ψ k r).map f ≫
        (leftPhiSourceExpectedIsoApp T ψ k r Y).hom =
      (leftPhiSourceExpectedIsoApp T ψ k r X).hom ≫
        (leftPhiExpectedPullback T k r ψ ⋙ SmoothRep.toRep).map f := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  rfl

private def _root_.Langlands.Derivative.MirabolicProductMinus.leftPhiSourceExpectedIso :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    leftPhiSourceInducedFunctor.{uF,uV} T ψ k r ≅
      leftPhiExpectedPullback T k r ψ ⋙ SmoothRep.toRep :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  NatIso.ofComponents (leftPhiSourceExpectedIsoApp T ψ k r)
    (leftPhiSourceExpectedIsoApp_natural T ψ k r)

set_option maxHeartbeats 800000 in
/-- The actual normalized left mixed product commutes naturally with source
Phi-minus, including both full input maps and the actual rank transports. -/
def leftPhiCompatibilityIso :
    letI := T.topology
    leftPhiProduct.{uF,uV} T ψ k (r + 1) ≅ leftPhiExpected T ψ k r := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 3)
  letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  let e₁ : leftPhiNormalizedIdentityPiece.{uF,uV} T ψ k r ≅
      leftPhiStabilizerLocalizedFunctor T ψ k r :=
    leftPhiStabilizerLocalizationIso T ψ k r
  exact Functor.fullyFaithfulCancelRight SmoothRep.toRep
    (leftPhiProductIdentityIso.{uF,uV} T ψ k r ≪≫ e₁ ≪≫
      leftPhiStabilizerSourceIso T ψ k r ≪≫ leftPhiSourceExpectedIso T ψ k r ≪≫
        Functor.isoWhiskerRight (leftPhiExpectedHostIso T k r ψ).symm SmoothRep.toRep)

/-- The exact higher-source-rank left-Phi clause of BZ77 4.13(b). -/
theorem leftPhiCompatibility : LeftPhiCompatibility.{uF,uV} F T := by
  let := T.topology
  intro ψ k r
  exact ⟨leftPhiCompatibilityIso T ψ k r⟩

end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
