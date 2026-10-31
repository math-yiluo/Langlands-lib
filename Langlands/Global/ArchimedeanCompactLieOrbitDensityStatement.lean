import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Global.ArchimedeanJointFinite

/-! # Density of the compact and enveloping orbit -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Every genuine group translate of a joint-finite smooth vector is
approximable in the actual derivative topology by finite linear combinations
of compact translates of its genuine enveloping derivatives. -/
def CompactLieOrbitDensityStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ f : DerivativeSmoothFunctions K n,
    IsJointFinite K n (DerivativeSmoothFunctions.toSmooth K n f) →
      ∀ g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K),
        DerivativeSmoothFunctions.rightAction K n g f ∈
          (Submodule.span ℂ (Set.range
            (fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
              DerivativeSmoothFunctions.rightAction K n p.1.val
                (DerivativeSmoothFunctions.operator K n p.2 f)))).topologicalClosure

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactLieOrbitDensityStatement

end Langlands.Global.ArchimedeanGL
