import Langlands.Automorphic.EnvelopingAction

/-! # Right-translation covariance of actual real differentiation -/

universe u

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Real directional differentiation on actual smooth archimedean functions
transforms under right translation by matrix conjugation `X ↦ g * X * g⁻¹`. -/
def SmoothRealDifferentialCovarianceStatement : Prop :=
  ∀ (g : InfiniteAdelicGL K n) (X : ArchimedeanGL.RealLieAlgebra K n)
    (f : ArchimedeanGL.SmoothFunctions K n),
    ArchimedeanGL.smoothRightAction K n g
        (ArchimedeanGL.smoothDifferential K n X f) =
      ArchimedeanGL.smoothDifferential K n
        ((ArchimedeanGL.realLieAlgebraToMatrix K n).symm
          ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
            ArchimedeanGL.realLieAlgebraToMatrix K n X *
            (archimedeanGLCoordinates K n g⁻¹ : ArchimedeanMatrix K n)))
        (ArchimedeanGL.smoothRightAction K n g f)

/-- The same real-generator covariance for the genuine enveloping action on
finite-smooth rational-invariant adelic functions. -/
def FiniteSmoothRealDifferentialCovarianceStatement : Prop :=
  ∀ (g : InfiniteAdelicGL K n) (X : ArchimedeanGL.RealLieAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n),
    finiteSmoothRightAction K n (AdelicGL.ofInfinite K n g)
        (finiteSmoothEnvelopingAction K n
          (ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n X)) f) =
      finiteSmoothEnvelopingAction K n
        (ArchimedeanGL.envelopingGenerator K n
          (ArchimedeanGL.complexify K n
            ((ArchimedeanGL.realLieAlgebraToMatrix K n).symm
              ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
                ArchimedeanGL.realLieAlgebraToMatrix K n X *
                (archimedeanGLCoordinates K n g⁻¹ : ArchimedeanMatrix K n)))))
        (finiteSmoothRightAction K n (AdelicGL.ofInfinite K n g) f)

/-- One proof target for smooth covariance and its finite-smooth slice descent,
in that order. -/
def RealDifferentialCovarianceStatement : Prop :=
  SmoothRealDifferentialCovarianceStatement K n ∧
    FiniteSmoothRealDifferentialCovarianceStatement K n

end Langlands.Automorphic
