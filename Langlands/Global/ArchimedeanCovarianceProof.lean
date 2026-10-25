import Langlands.Global.ArchimedeanCovarianceStatement
import Langlands.Automorphic.RealDifferentialCovarianceProof

/-! # Covariance of the actual enveloping and center differential actions -/

noncomputable section

universe u

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Complex linearity extends the published real-generator covariance to the
whole complexified Lie algebra. -/
theorem smoothRightAction_complexSmoothLieAction
    (g : InfiniteAdelicGL K n) (X : ComplexLieAlgebra K n) (f : SmoothFunctions K n) :
    smoothRightAction K n g (complexSmoothLieAction K n X f) =
      complexSmoothLieAction K n (complexLieConjugation K n g X)
        (smoothRightAction K n g f) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexSmoothLieAction_tmul, complexLieConjugation_tmul,
      LinearMap.smul_apply, map_smul]
    rw [smoothRightAction_smoothDifferential_realLieConjugation]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply, hX, hY]

/-- Right translation intertwines every actual enveloping differential operator
with its adjoint conjugate. -/
theorem envelopingRightCovariance : EnvelopingRightCovarianceStatement K n := by
  intro g a
  refine Quotient.inductionOn a ?_
  intro t
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra K n)
  change ∀ f : SmoothFunctions K n,
    smoothRightAction K n g (envelopingAction K n (q t) f) =
      envelopingAction K n (envelopingConjugation K n g (q t))
        (smoothRightAction K n g f)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    intro f
    simp [Algebra.algebraMap_eq_smul_one]
  | ι X =>
    intro f
    change smoothRightAction K n g
        (envelopingAction K n (envelopingGenerator K n X) f) =
      envelopingAction K n
        (envelopingConjugation K n g (envelopingGenerator K n X))
        (smoothRightAction K n g f)
    simpa only [envelopingAction_generator, envelopingConjugation_generator] using
      smoothRightAction_complexSmoothLieAction K n g X f
  | mul a b ha hb =>
    intro f
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, hb]
  | add a b ha hb =>
    intro f
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Restrict enveloping covariance through the actual center inclusion. -/
theorem centerRightCovariance : CenterRightCovarianceStatement K n := by
  intro g z f
  simpa only [centerAction_apply, centerInclusion_centerConjugation] using
    envelopingRightCovariance K n g (centerInclusion K n z) f

/-- The ordered conjunction of enveloping covariance and center covariance. -/
theorem envelopingCenterRightCovariance :
    EnvelopingCenterRightCovarianceStatement K n :=
  ⟨envelopingRightCovariance K n, centerRightCovariance K n⟩

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    EnvelopingCenterRightCovarianceStatement K n :=
  @envelopingCenterRightCovariance

end Langlands.Global.ArchimedeanGL
