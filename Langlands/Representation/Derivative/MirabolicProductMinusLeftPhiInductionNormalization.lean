import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
import Langlands.Representation.Induction.CharacterTwistProof

/-! Moving the actual ambient Phi normalization into compactly induced coefficients. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  HarmonicAnalysis Induction

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
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

/-- Compact induction of the complete actual normalized left cycle coefficient
has zero carrier. -/
theorem leftPhiNormalizedInduced_zero_subsingleton :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    Subsingleton
      (CompactFunctions ((leftStages k r F.Carrier 0).comap plusSuccessor)
        (leftPhiNormalizedStagesAction T k r ρ τ ψ 0)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 2)
  let := leftPhiNormalizedStagesQuotient_zero_subsingleton T k r ρ τ ψ
  infer_instance

end Langlands.Derivative.MirabolicProductMinus
