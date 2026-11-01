import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison

/-! The entire normalized identity-orbit localization and its actual lower product. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis Induction
  Induction.SplitKernelLocalization MixedProductTensor Geometric

universe uF uV uW uV' uW'

private theorem identityTwistEquiv_apply {G U X : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    (χ : G →* ℂˣ) {σ : Representation ℂ G U} {τ : Representation ℂ G X}
    (e : σ.Equiv τ) (x : U) : twistEquiv χ e x = e x := rfl

private theorem identityTwistMap_apply {G U X : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    (χ : G →* ℂˣ) {σ : Representation ℂ G U} {τ : Representation ℂ G X}
    (f : σ.IntertwiningMap τ) (x : U) : twistIntertwining χ f x = f x := rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (k r : ℕ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
variable (τ : Representation ℂ (mirabolic (r + 1) F.Carrier) W)

/-- The full higher covariance-normalized stabilizer coefficient is smooth,
by continuous restriction of the actual smooth twisted inducing coefficient. -/
theorem leftPhiNormalizedStabilizer_smooth
    (hρ : letI := T.topology; IsSmooth ρ)
    (hτ : letI := T.topology; IsSmooth τ) (i : Fin 2) :
    letI := T.topology
    IsSmooth (leftPhiNormalizedStabilizer T k r ρ τ i) := by
  let := T.topology
  let := isTopologicalRing_of_topologicalData F T
  change IsSmooth
    (((twist (T.leftCharacter (k + 1) (r + 1)).toMonoidHom
      (leftInducingRepresentation ρ τ)).comp (leftInducingHom k r F.Carrier)).comp
        (stabilizerToInducing (leftInducing k r F.Carrier)
          (plusSubgroup (k + r + 1) F.Carrier) (leftRepresentative k r F.Carrier i)))
  exact isSmooth_comp _
    (continuous_stabilizerToInducing (leftInducing k r F.Carrier)
      (leftRepresentative k r F.Carrier i))
    (isSmooth_comp _ (continuous_leftInducingHom k r F.Carrier)
      ((isSmooth_twist_iff _ _ (T.leftCharacter (k + 1) (r + 1)).isOpen_ker).mpr
        (isSmooth_leftInducingRepresentation hρ hτ)))

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
variable (B : letI := T.topology
  SmoothRep.{0, uF, uW} ℂ (mirabolic (r + 1) F.Carrier))

/-- Positive-character localization of the entire identity-orbit induction,
including the ambient inverse-half twist, is the actual lower source-Phi
compact induction in the proved rank-pullback coordinates. -/
def leftPhiIdentityNormalizedEquiv (hρ : letI := T.topology; IsSmooth ρ) :
    letI := T.topology
    letI := T.fieldT2
    letI := isTopologicalRing_of_topologicalData F T
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    Representation.Equiv
      (twist (Mirabolic.phiMinusCharacter T (k + r + 1))
        (localizedAction
          (plusProjection (n := k + r + 1) (F := F.Carrier))
          (plusSuccessor (n := k + r + 1) (F := F.Carrier))
          (plusKernelTheta ψ (k + r + 1))
          (plusKernelTheta_sectionInvariant ψ (k + r + 1))
          (compactInduced (leftStabilizer k r F.Carrier 1)
            (leftPhiNormalizedStabilizer T k r ρ B.representation 1))))
      ((compactInduced (leftSubgroup (k + 1) r F.Carrier)
        (leftPhiSourceCoefficient T k r ψ ρ B)).comp
          (leftPhiLowerRankEquiv k r F.Carrier).toMonoidHom) := by
  let := T.topology
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearTopologicalGroup (k + r + 2)
  let := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  exact ((twistEquiv (Mirabolic.phiMinusCharacter T (k + r + 1))
    (padic_leftPhiStagesCharacterEquiv T ψ k r 1
      (leftPhiNormalizedStabilizer T k r ρ B.representation 1)
      (leftPhiNormalizedStabilizer_smooth T k r ρ B.representation hρ B.isSmooth 1))).trans
    (leftPhiAmbientInductionEquiv T k r ψ ρ B.representation 1)).trans
      (leftPhiCompactSourceEquiv T k r ψ ρ B)

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {ρ' : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V'}
variable {B' : letI := T.topology
  SmoothRep.{0, uF, uW'} ℂ (mirabolic (r + 1) F.Carrier)}

set_option maxHeartbeats 800000 in
/-- The composed normalized identity-orbit equivalence commutes with both
actual input intertwiners on every localization class, across four independent
coefficient universes. -/
theorem leftPhiIdentityNormalizedEquiv_natural
    (hρ : letI := T.topology; IsSmooth ρ)
    (hρ' : letI := T.topology; IsSmooth ρ')
    (f : ρ.IntertwiningMap ρ')
    (g : letI := T.topology; B.representation.IntertwiningMap B'.representation)
    (z : letI := T.topology
      letI := T.fieldT2
      letI := isTopologicalRing_of_topologicalData F T
      Jacquet.Localization.Coinvariants
        (compactInduced (leftStabilizer k r F.Carrier 1)
          (leftPhiNormalizedStabilizer T k r ρ B.representation 1))
        (plusProjection (n := k + r + 1) (F := F.Carrier)).ker
        (plusKernelTheta ψ (k + r + 1))) :
    letI := T.topology
    letI := T.fieldT2
    letI := isTopologicalRing_of_topologicalData F T
    letI := T.generalLinearTopologicalGroup (k + r + 2)
    letI := T.generalLinearTopologicalGroup (k + 1 + r + 1)
    leftPhiIdentityNormalizedEquiv T k r ρ' ψ B' hρ'
        (twistIntertwining (Mirabolic.phiMinusCharacter T (k + r + 1))
          (sectionMap
            (plusProjection (n := k + r + 1) (F := F.Carrier))
            (plusSuccessor (n := k + r + 1) (F := F.Carrier))
            (plusKernelTheta ψ (k + r + 1))
            (plusKernelTheta_sectionInvariant ψ (k + r + 1))
            (compactInducedMap (leftStabilizer k r F.Carrier 1)
              (leftPhiNormalizedStabilizerMap T k r ρ B.representation f g 1))) z) =
      pullbackMap (leftPhiLowerRankEquiv k r F.Carrier).toMonoidHom
        (compactInducedMap (leftSubgroup (k + 1) r F.Carrier)
          (leftPhiSourceCoefficientMap T k r ψ ρ B f g))
        (leftPhiIdentityNormalizedEquiv T k r ρ ψ B hρ z) := by
  let := T.topology
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearTopologicalGroup (k + r + 2)
  let := T.generalLinearTopologicalGroup (k + 1 + r + 1)
  simp only [leftPhiIdentityNormalizedEquiv, Representation.Equiv.trans_apply,
    identityTwistEquiv_apply, identityTwistMap_apply, pullbackMap_apply]
  have hs := padic_leftPhiStagesCharacterEquiv_natural T ψ k r 1
    (σ := leftPhiNormalizedStabilizer T k r ρ B.representation 1)
    (τ := leftPhiNormalizedStabilizer T k r ρ' B'.representation 1)
    (leftPhiNormalizedStabilizer_smooth T k r ρ B.representation hρ B.isSmooth 1)
    (leftPhiNormalizedStabilizer_smooth T k r ρ' B'.representation hρ' B'.isSmooth 1)
    (leftPhiNormalizedStabilizerMap T k r ρ B.representation f g 1) z
  have ha := leftPhiAmbientInductionEquiv_natural T k r ψ ρ B.representation f g 1
    (padic_leftPhiStagesCharacterEquiv T ψ k r 1
      (leftPhiNormalizedStabilizer T k r ρ B.representation 1)
      (leftPhiNormalizedStabilizer_smooth T k r ρ B.representation hρ B.isSmooth 1) z)
  have hc := leftPhiCompactSourceEquiv_natural T k r ψ ρ B f g
    (leftPhiAmbientInductionEquiv T k r ψ ρ B.representation 1
      (padic_leftPhiStagesCharacterEquiv T ψ k r 1
        (leftPhiNormalizedStabilizer T k r ρ B.representation 1)
        (leftPhiNormalizedStabilizer_smooth T k r ρ B.representation hρ B.isSmooth 1) z))
  have h₁ := congrArg (fun x => leftPhiCompactSourceEquiv T k r ψ ρ' B'
    (leftPhiAmbientInductionEquiv T k r ψ ρ' B'.representation 1 x)) hs
  have h₂ := congrArg (fun x => leftPhiCompactSourceEquiv T k r ψ ρ' B' x) ha
  have h₃ := h₂.trans hc
  have h₄ := h₁.trans h₃
  with_reducible exact h₄

end Langlands.Derivative.MirabolicProductMinus
