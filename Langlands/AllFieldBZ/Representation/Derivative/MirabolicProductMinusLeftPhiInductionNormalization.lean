import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding leftPhiAmbientInductionEquiv leftPhiAmbientInductionEquiv_eval leftPhiAmbientInductionEquiv_natural leftPhiAmbientSectionCharacter leftPhiCharacter_rankCast_symm leftPhiNormalizedRadicalEquiv leftPhiNormalizedRadicalEquiv_mk leftPhiNormalizedSection_scalar leftPhiNormalizedStabilizer leftPhiNormalizedStabilizerMap leftPhiNormalizedStabilizer_radical leftPhiNormalizedStagesAction leftPhiNormalizedStagesCoefficientEquiv leftPhiNormalizedStagesCoefficientEquiv_action_mk leftPhiNormalizedStagesCoefficientEquiv_mk leftPhiNormalizedStagesCoefficientEquiv_natural leftPhiNormalizedStagesCoefficientEquiv_one_tmul leftPhiNormalizedStagesMap leftPhiNormalizedStagesMap_mk leftPhiNormalizedStagesQuotient leftPhiNormalizedStagesQuotient_zero_subsingleton leftPhiNormalizedStagesTensorEquiv leftPhiNormalizedStagesTensorEquiv_action_tmul leftPhiNormalizedStagesTensorEquiv_mk_tmul leftPhiNormalizedStagesTensorEquiv_natural leftPhiSectionCharacter leftPhiSectionCharacter_apply leftPhiSectionCharacter_eq leftPhiStabilizerCharacter leftPhiStabilizerCharacter_radical leftPhiSubgroup_determinantNorm
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.HarmonicAnalysis
open Langlands.Induction
universe uF uV uW uV' uW'

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (k r : ℕ) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
variable (τ : Representation ℂ (mirabolic (r + 1) F.Carrier) W)

/-- The actual ambient inverse-half character moves into the entire actual
stages coefficient of compact induction, at either left orbit. -/
def leftPhiAmbientInductionEquiv (i : Fin 2) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    Representation.Equiv
      (twist (Mirabolic.phiMinusCharacter T (k + r + 1))
        (compactInduced ((leftStages k r F.Carrier i).comap plusSuccessor)
          (leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i))))
      (compactInduced ((leftStages k r F.Carrier i).comap plusSuccessor)
        (leftPhiNormalizedStagesAction T k r ρ τ ψ i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 2)
  compactInductionTwistEquiv
    ((leftStages k r F.Carrier i).comap plusSuccessor)
    ⟨Mirabolic.phiMinusCharacter T (k + r + 1),
      Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)⟩
    (leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i))

/-- The induced equivalence multiplies the entire original function by the
actual ambient inverse-half character. -/
@[simp] theorem leftPhiAmbientInductionEquiv_eval (i : Fin 2)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 2)
      CompactFunctions ((leftStages k r F.Carrier i).comap plusSuccessor)
        (leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i)))
    (l : mirabolic (k + r + 1) F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    eval ((leftStages k r F.Carrier i).comap plusSuccessor)
        (leftPhiNormalizedStagesAction T k r ρ τ ψ i)
        (leftPhiAmbientInductionEquiv T k r ψ ρ τ i f).val l =
      (Mirabolic.phiMinusCharacter T (k + r + 1) l : ℂ) •
        eval ((leftStages k r F.Carrier i).comap plusSuccessor)
          (leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i))
          f.val l := rfl

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V'}
variable {τ' : Representation ℂ (mirabolic (r + 1) F.Carrier) W'}

/-- Ambient character multiplication commutes with the two actual input maps,
on every compactly induced function across independent carrier universes. -/
theorem leftPhiAmbientInductionEquiv_natural
    (f : ρ.IntertwiningMap ρ') (g : τ.IntertwiningMap τ') (i : Fin 2)
    (z : letI := T.topology
      letI := T.generalLinearTopologicalGroup (k + r + 2)
      CompactFunctions ((leftStages k r F.Carrier i).comap plusSuccessor)
        (leftPhiStagesAction k r ψ i (leftPhiNormalizedStabilizer T k r ρ τ i))) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    leftPhiAmbientInductionEquiv T k r ψ ρ' τ' i
        (compactInducedMap ((leftStages k r F.Carrier i).comap plusSuccessor)
          (leftPhiStagesMap k r ψ i
            (leftPhiNormalizedStabilizerMap T k r ρ τ f g i)) z) =
      compactInducedMap ((leftStages k r F.Carrier i).comap plusSuccessor)
        (leftPhiNormalizedStagesMap T k r ρ τ ψ f g i)
        (leftPhiAmbientInductionEquiv T k r ψ ρ τ i z) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 2)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  exact ((leftPhiStagesMap k r ψ i
    (leftPhiNormalizedStabilizerMap T k r ρ τ f g i)).toLinearMap.map_smul
      (Mirabolic.phiMinusCharacter T (k + r + 1) l : ℂ) _).symm

end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
