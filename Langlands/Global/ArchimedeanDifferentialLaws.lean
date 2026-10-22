import Langlands.Global.ArchimedeanDifferentialGeometry

/-! # Operator laws for the genuine smooth archimedean differential -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual directional operators respect the matrix commutator. -/
def SmoothDifferentialCommutator : Prop :=
  ∀ X Y : RealLieAlgebra K n,
    smoothDifferential K n ⁅X, Y⁆ =
      (smoothDifferential K n X).comp (smoothDifferential K n Y) -
        (smoothDifferential K n Y).comp (smoothDifferential K n X)

/-- The actual directional operators commute with pullback by left multiplication. -/
def SmoothDifferentialLeftTranslation : Prop :=
  ∀ (X : RealLieAlgebra K n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)),
    (smoothDifferential K n X).comp (smoothLeftTranslation K n a) =
      (smoothLeftTranslation K n a).comp (smoothDifferential K n X)

/-- The two operator laws needed to construct and descend the Lie action. -/
def SmoothDifferentialLaws : Prop :=
  SmoothDifferentialCommutator K n ∧ SmoothDifferentialLeftTranslation K n

end Langlands.Global.ArchimedeanGL
