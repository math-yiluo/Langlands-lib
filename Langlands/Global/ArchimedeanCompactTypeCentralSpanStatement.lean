import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Global.ArchimedeanCenterFinite

/-! # Finite center-span coverings of actual generated compact types -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Each actual compact type in a compact-finitely generated differential module
is covered by finitely many full center orbits of vectors of that module. -/
def CompactTypeCentralSpanStatement : Prop :=
  ∀ f : DerivativeSmoothFunctions K n,
    Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f →
    ∀ σ : CompactType K n,
      let M : Submodule ℂ (DerivativeSmoothFunctions K n) :=
        Submodule.span ℂ
          (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
            compactAction K n p.1 (operator K n p.2 f))
      ∃ m : ℕ, ∃ v : Fin m → M,
        compactTypeSubmodule σ ⊓ M ≤
          ⨆ i : Fin m, (centerOrbitSpan K n (toSmooth K n (v i).val)).map
            (toSmooth K n).symm.toLinearMap

end Langlands.Global.ArchimedeanGL
