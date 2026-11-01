import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction

/-! The normalized identity-orbit coefficient is the actual source-Phi coefficient. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  GeneralLinear.Mirabolic.MixedProduct HarmonicAnalysis Induction
  Jacquet.Localization MixedProductTensor

universe uF uV uW uV' uW'

section LowerSection

variable (k r : ℕ) (R : Type uF) [CommRing R]

/-- The actual identity stages section in the lower mixed-product coordinates,
including the proved mirabolic rank transport. -/
def leftPhiLowerSectionEquiv :
    (leftStages k r R 1).comap plusSuccessor ≃* leftSubgroup (k + 1) r R :=
  (leftPhiStagesSectionEquiv k r 1).trans (leftIdentitySectionEquiv k r R)

variable [TopologicalSpace R]

theorem continuous_leftPhiLowerSectionEquiv :
    Continuous (leftPhiLowerSectionEquiv k r R) := by
  have hc : Continuous (leftPhiStagesSectionEquiv k r (R := R) 1) := by
    exact continuous_subtype_val.subtype_mk _
  change Continuous ((leftIdentitySectionEquiv k r R) ∘
    (leftPhiStagesSectionEquiv k r (R := R) 1))
  exact (continuous_leftIdentitySectionEquiv k r R).comp hc

theorem continuous_leftPhiLowerSectionEquiv_symm :
    Continuous (leftPhiLowerSectionEquiv k r R).symm :=
  (continuous_subtype_val.subtype_mk _).comp
    (continuous_leftIdentitySectionEquiv_symm k r R)

end LowerSection

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
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

end Langlands.Derivative.MirabolicProductMinus
