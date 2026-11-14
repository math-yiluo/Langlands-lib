import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding leftPhiAmbientSectionCharacter leftPhiCharacter_rankCast_symm leftPhiHigherSectionMap leftPhiHigherSectionRepresentation leftPhiNormalizedRadicalEquiv leftPhiNormalizedRadicalEquiv_mk leftPhiNormalizedSection_scalar leftPhiNormalizedSourceEquiv leftPhiNormalizedSourceEquiv_mk_tmul leftPhiNormalizedSourceEquiv_natural leftPhiNormalizedSource_action_tmul leftPhiNormalizedStabilizer leftPhiNormalizedStabilizerMap leftPhiNormalizedStabilizer_radical leftPhiNormalizedStagesAction leftPhiNormalizedStagesCoefficientEquiv leftPhiNormalizedStagesCoefficientEquiv_action_mk leftPhiNormalizedStagesCoefficientEquiv_mk leftPhiNormalizedStagesCoefficientEquiv_natural leftPhiNormalizedStagesCoefficientEquiv_one_tmul leftPhiNormalizedStagesMap leftPhiNormalizedStagesMap_mk leftPhiNormalizedStagesQuotient leftPhiNormalizedStagesQuotient_zero_subsingleton leftPhiNormalizedStagesTensorEquiv leftPhiNormalizedStagesTensorEquiv_action_tmul leftPhiNormalizedStagesTensorEquiv_mk_tmul leftPhiNormalizedStagesTensorEquiv_natural leftPhiSectionCharacter leftPhiSectionCharacter_apply leftPhiSectionCharacter_eq leftPhiSourceCoefficient leftPhiSourceCoefficientMap leftPhiSourceCoefficient_tmul_quotient leftPhiSourceQuotient leftPhiSourceQuotient_factor leftPhiSourceQuotient_naturality leftPhiSourceQuotient_surjective leftPhiSourceQuotient_tmul leftPhiStabilizerCharacter leftPhiStabilizerCharacter_radical leftPhiSubgroup_determinantNorm leftPhiTransportedSourceCoefficient leftPhiTransportedSourceMap
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.HarmonicAnalysis
open Langlands.Induction
open Langlands.Jacquet.Localization
open Langlands.MixedProductTensor
universe uF uV uW uV' uW'

section LowerSection
variable (k r : ℕ) (R : Type uF) [CommRing R]

variable [TopologicalSpace R]

end LowerSection
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (k r : ℕ) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
variable (B : letI := T.topology
  SmoothRep.{0, uF, uW} ℂ (mirabolic (r + 1) F.Carrier))

/-- The actual normalized lower source coefficient pulled back through the full
identity section and its actual rank transport. -/
def leftPhiTransportedSourceCoefficient :
    letI := T.topology
    Representation ℂ ((leftStages k r F.Carrier 1).comap plusSuccessor)
      (V ⊗[ℂ] (Mirabolic.phiMinus T ψ r).obj B) :=
  letI := T.topology
  (leftPhiSourceCoefficient T k r ψ ρ B).comp
    (leftPhiLowerSectionEquiv k r F.Carrier).toMonoidHom

/-- The complete normalized coefficient identification intertwines the actual
lower source coefficient on every pure-tensor quotient class. -/
theorem leftPhiNormalizedSource_action_tmul
    (l : (leftStages k r F.Carrier 1).comap plusSuccessor) (v : V) (w : B) :
    letI := T.topology
    leftPhiNormalizedStagesTensorEquiv T k r ρ B.representation ψ
        (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1 l
          (mk _ _ _ (v ⊗ₜ[ℂ] w))) =
      leftPhiTransportedSourceCoefficient T k r ψ ρ B l
        (v ⊗ₜ[ℂ] Mirabolic.phiMinusQuotient T ψ r B w) := by
  let := T.topology
  exact (leftPhiNormalizedStagesTensorEquiv_action_tmul T k r ρ B.representation ψ
    l v w).trans
      (leftPhiSourceCoefficient_tmul_quotient T k r ψ ρ B
        (leftPhiLowerSectionEquiv k r F.Carrier l) v w).symm

/-- The full normalized identity-orbit coefficient is representation-equivalent
to the actual source-Phi coefficient through its proved rank transport. -/
def leftPhiNormalizedSourceEquiv :
    letI := T.topology
    Representation.Equiv (leftPhiNormalizedStagesAction T k r ρ B.representation ψ 1)
      (leftPhiTransportedSourceCoefficient T k r ψ ρ B) :=
  letI := T.topology
  {
    toLinearEquiv := leftPhiNormalizedStagesTensorEquiv T k r ρ B.representation ψ
    isIntertwining' l := by
      apply hom_ext
      apply TensorProduct.ext'
      intro v w
      exact leftPhiNormalizedSource_action_tmul T k r ψ ρ B l v w
  }

@[simp] theorem leftPhiNormalizedSourceEquiv_mk_tmul (v : V) (w : B) :
    letI := T.topology
    leftPhiNormalizedSourceEquiv T k r ψ ρ B (mk _ _ _ (v ⊗ₜ[ℂ] w)) =
      v ⊗ₜ[ℂ] Mirabolic.phiMinusQuotient T ψ r B w := rfl

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V'}
variable {B' : letI := T.topology
  SmoothRep.{0, uF, uW'} ℂ (mirabolic (r + 1) F.Carrier)}

/-- Every pair of input intertwiners induces the actual map of the transported
normalized source coefficient, with independent target universes. -/
def leftPhiTransportedSourceMap
    (f : ρ.IntertwiningMap ρ') (g : letI := T.topology
      B.representation.IntertwiningMap B'.representation) :
    letI := T.topology
    (leftPhiTransportedSourceCoefficient T k r ψ ρ B).IntertwiningMap
      (leftPhiTransportedSourceCoefficient T k r ψ ρ' B') :=
  letI := T.topology
  pullbackMap (leftPhiLowerSectionEquiv k r F.Carrier).toMonoidHom
    (leftPhiSourceCoefficientMap T k r ψ ρ B f g)

/-- The representation comparison is natural on the entire actual normalized
quotient in both factors, across four independent carrier universes. -/
theorem leftPhiNormalizedSourceEquiv_natural
    (f : ρ.IntertwiningMap ρ') (g : letI := T.topology
      B.representation.IntertwiningMap B'.representation)
    (z : letI := T.topology
      leftPhiNormalizedStagesQuotient T k r ρ B.representation ψ 1) :
    letI := T.topology
    leftPhiNormalizedSourceEquiv T k r ψ ρ' B'
        (leftPhiNormalizedStagesMap T k r ρ B.representation ψ f g 1 z) =
      leftPhiTransportedSourceMap T k r ψ ρ B f g
        (leftPhiNormalizedSourceEquiv T k r ψ ρ B z) := by
  let := T.topology
  exact leftPhiNormalizedStagesTensorEquiv_natural T k r ρ B.representation ψ f g z

end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
