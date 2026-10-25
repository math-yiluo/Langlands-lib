import Langlands.Global.ArchimedeanAdjoint
import Langlands.Global.ArchimedeanEnvelopingAction

/-! # Right-translation covariance of the actual enveloping and center actions -/

universe u

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Right translation intertwines the actual enveloping differential action of `a`
with that of its adjoint image `Ad(g) a`, where `Ad(g) X = g * X * g⁻¹`. -/
def EnvelopingRightCovarianceStatement : Prop :=
  ∀ (g : InfiniteAdelicGL K n) (a : EnvelopingAlgebra K n) (f : SmoothFunctions K n),
    smoothRightAction K n g (envelopingAction K n a f) =
      envelopingAction K n (envelopingConjugation K n g a) (smoothRightAction K n g f)

/-- Right translation intertwines the actual center action of `z` with that of its
image under the restricted adjoint automorphism of the enveloping center. -/
def CenterRightCovarianceStatement : Prop :=
  ∀ (g : InfiniteAdelicGL K n) (z : EnvelopingCenter K n) (f : SmoothFunctions K n),
    smoothRightAction K n g (centerAction K n z f) =
      centerAction K n (centerConjugation K n g z) (smoothRightAction K n g f)

/-- One proof target for enveloping covariance and its center restriction,
in that order. -/
def EnvelopingCenterRightCovarianceStatement : Prop :=
  EnvelopingRightCovarianceStatement K n ∧ CenterRightCovarianceStatement K n

end Langlands.Global.ArchimedeanGL
