import Langlands.Global.ArchimedeanSmoothTopology

/-! # Smooth scalar coefficients of actual right-translation orbits -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- A continuous complex linear functional on the actual derivative topology
turns every smooth right-translation orbit into an actual smooth function.
Every genuine enveloping derivative acts on the vector inside the coefficient. -/
def SmoothOrbitCoefficientStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (f : DerivativeSmoothFunctions K n),
    ∃ F : SmoothFunctions K n,
      (∀ g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K),
        F.val g = ℓ ((DerivativeSmoothFunctions.toSmooth K n).symm
          (smoothRightAction K n g (DerivativeSmoothFunctions.toSmooth K n f)))) ∧
      ∀ (a : EnvelopingAlgebra K n)
        (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)),
        (envelopingAction K n a F).val g =
          ℓ ((DerivativeSmoothFunctions.toSmooth K n).symm
            (smoothRightAction K n g
              (envelopingAction K n a (DerivativeSmoothFunctions.toSmooth K n f))))

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @SmoothOrbitCoefficientStatement

end Langlands.Global.ArchimedeanGL
