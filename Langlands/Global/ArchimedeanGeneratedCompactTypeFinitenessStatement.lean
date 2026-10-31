import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Global.ArchimedeanCenterFinite

/-! # Finite compact types in an actual generated differential module -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Each compact type in the algebraic compact-and-enveloping module generated
by a compact-finite and center-finite smooth function is finite-dimensional. -/
def GeneratedCompactTypeFinitenessStatement : Prop :=
  ∀ f : DerivativeSmoothFunctions K n,
    Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f →
    IsCenterFinite K n (toSmooth K n f) →
    ∀ σ : CompactType K n,
      Module.Finite ℂ
        ((compactTypeSubmodule σ ⊓
          Submodule.span ℂ
            (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
              compactAction K n p.1 (operator K n p.2 f))) :
          Submodule ℂ (DerivativeSmoothFunctions K n))

end Langlands.Global.ArchimedeanGL
