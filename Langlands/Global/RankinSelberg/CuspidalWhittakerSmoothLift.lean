import Langlands.Global.ArchimedeanFunctionalOrbitLift
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerRegularity
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof

/-! # The actual cuspidal Whittaker lift to smooth archimedean functions -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global.ArchimedeanGL NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup
  regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
  (hψ : IsStandardAdditiveCharacter F ψ) (b : FiniteAdelicGL F (r + 1))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))

include hψ in
private theorem contMDiff_cuspWhittaker_adelicPoint (v : T.Space) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g : ArchimedeanGL F (r + 1) =>
      cuspWhittaker F T ψ v (adelicPoint F (r + 1) g b)) := by
  have h : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ (archWhittakerExt T ψ v b)
      {g : ArchimedeanMatrix F (r + 1) | IsUnit g} :=
    (contDiffOn_archWhittakerExt T ψ hψ v b).contMDiffOn
  have ho : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g : ArchimedeanGL F (r + 1) =>
      archWhittakerExt T ψ v b (g : ArchimedeanMatrix F (r + 1))) := by
    apply contMDiffOn_univ.mp
    exact h.comp (Units.contMDiff_val (n := ∞)).contMDiffOn
      (fun g _ => Units.isUnit g)
  exact ho.congr fun g => (archWhittakerExt_units T ψ hψ v b g).symm

/-- The original Whittaker integral in the infinite variable, at a fixed
finite adelic argument. -/
def whittakerSmoothLift : T.Space →ₗ[ℂ] SmoothFunctions F (r + 1) :=
  (LinearMap.pi fun a : InfiniteAdelicGL F (r + 1) =>
    UnramifiedWhittaker.whittakerFunctional F ψ hψ T
      (adelicPoint F (r + 1) (archimedeanGLCoordinates F (r + 1) a) b)).codRestrict
      (smoothFunctions F (r + 1)) fun v => by
    change ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g : ArchimedeanGL F (r + 1) =>
      cuspWhittaker F T ψ v (adelicPoint F (r + 1)
        (archimedeanGLCoordinates F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm g)) b))
    simpa only [ContinuousMulEquiv.apply_symm_apply] using
      contMDiff_cuspWhittaker_adelicPoint T ψ hψ b v

@[simp]
theorem whittakerSmoothLift_apply (v : T.Space) (a : InfiniteAdelicGL F (r + 1)) :
    (whittakerSmoothLift T ψ hψ b v).val a =
      cuspWhittaker F T ψ v (adelicPoint F (r + 1) (archimedeanGLCoordinates F (r + 1) a) b) :=
  rfl

private theorem archWhittakerExt_eq_lift (v : T.Space) (g : ArchimedeanGL F (r + 1)) :
    archWhittakerExt T ψ v b (g : ArchimedeanMatrix F (r + 1)) =
      (whittakerSmoothLift T ψ hψ b v).val ((archimedeanGLCoordinates F (r + 1)).symm g) := by
  rw [whittakerSmoothLift_apply, ContinuousMulEquiv.apply_symm_apply]
  exact archWhittakerExt_units T ψ hψ v b g

private theorem whittakerSmoothLift_realGenerator (X : RealLieAlgebra F (r + 1)) (w : T.Space) :
    whittakerSmoothLift T ψ hψ b (T.realization.envelopingAction
      (envelopingGenerator F (r + 1) (complexify F (r + 1) X)) w) =
    envelopingAction F (r + 1) (envelopingGenerator F (r + 1) (complexify F (r + 1) X))
      (whittakerSmoothLift T ψ hψ b w) := by
  apply Subtype.ext
  funext g
  let y := archimedeanGLCoordinates F (r + 1) g
  let Z := realLieAlgebraToMatrix F (r + 1) X
  let a := envelopingGenerator F (r + 1) (complexify F (r + 1) X)
  let C := whittakerSmoothLift T ψ hψ b
  have ha : Unfolding.matrixGenerator F (r + 1) Z = a :=
    congrArg (fun Y => envelopingGenerator F (r + 1) (complexify F (r + 1) Y))
      ((realLieAlgebraToMatrix F (r + 1)).symm_apply_apply X)
  have hw : lieDeriv T Z w = T.realization.envelopingAction a w :=
    congrArg (fun D => T.realization.envelopingAction D w) ha
  symm
  calc
    _ = (smoothDifferential F (r + 1) X (C w)).val g :=
      congrArg (fun A : Module.End ℂ (SmoothFunctions F (r + 1)) => (A (C w)).val g)
        (envelopingAction_real_generator F (r + 1) X)
    _ = fderiv ℝ (archWhittakerExt T ψ w b) (y : ArchimedeanMatrix F (r + 1))
        ((y : ArchimedeanMatrix F (r + 1)) * Z) :=
      smoothDifferential_eq_of_extension F (r + 1) X (C w)
        (archWhittakerExt T ψ w b) (archWhittakerExt_eq_lift T ψ hψ b w) g
    _ = archWhittakerExt T ψ (lieDeriv T Z w) b (y : ArchimedeanMatrix F (r + 1)) :=
      fderiv_archWhittakerExt_mul T ψ hψ w b y Z
    _ = (C (lieDeriv T Z w)).val ((archimedeanGLCoordinates F (r + 1)).symm y) :=
      archWhittakerExt_eq_lift T ψ hψ b (lieDeriv T Z w) y
    _ = (C (T.realization.envelopingAction a w)).val g :=
      (congrArg (fun z : T.Space => (C z).val _) hw).trans
        (congrArg (C (T.realization.envelopingAction a w)).val
          ((archimedeanGLCoordinates F (r + 1)).symm_apply_apply g))

/-- The actual integral lift intertwines every original enveloping operator. -/
theorem whittakerSmoothLift_envelopingAction (a : EnvelopingAlgebra F (r + 1)) (v : T.Space) :
    whittakerSmoothLift T ψ hψ b (T.realization.envelopingAction a v) =
      envelopingAction F (r + 1) a (whittakerSmoothLift T ψ hψ b v) :=
  envelopingCovariance_of_realGenerators F (r + 1) (V := T.Space)
    T.realization.envelopingAction (whittakerSmoothLift T ψ hψ b)
    (whittakerSmoothLift_realGenerator T ψ hψ b) a v

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
