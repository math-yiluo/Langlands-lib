import Langlands.Global.ArchimedeanCompactTypeClosureTransfer
import Langlands.Global.ArchimedeanGeneratedCompactFinite
import Langlands.Global.ArchimedeanGeneratedCompactTypeFinitenessProof
import Langlands.Global.ArchimedeanCompactLieOrbitDensityStatement
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanSeparateJointFiniteProof

/-! # Conditional finite compact types in the closed group orbit span -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The closure of the actual generated differential module has no new
vectors of a compact type, using the proved algebraic finite multiplicity. -/
theorem generatedCompactType_inf_topologicalClosure_eq
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f))
    (σ : CompactType K n) :
    (Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        compactAction K n p.1 (operator K n p.2 f))).topologicalClosure ⊓
        compactTypeSubmodule σ =
      Submodule.span ℂ
        (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
          compactAction K n p.1 (operator K n p.2 f)) ⊓
        compactTypeSubmodule σ := by
  let M : Submodule ℂ (DerivativeSmoothFunctions K n) :=
    Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        compactAction K n p.1 (operator K n p.2 f))
  have : Module.Finite ℂ
      (M ⊓ compactTypeSubmodule σ : Submodule ℂ (DerivativeSmoothFunctions K n)) := by
    rw [inf_comm]
    exact generatedCompactTypeFiniteness K n f hf hz σ
  exact compactType_inf_topologicalClosure_eq K n M
    (fun k _ hx => compactAction_mem_generatedCompactDifferentialSpan K n f k hx)
    (generatedCompactDifferentialSpan_compactFinite K n f hf) σ

/-- The actual closed generated differential module has finite-dimensional
compact-type intersections using the proved algebraic finite multiplicity. -/
theorem generatedCompactType_topologicalClosure_finite
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f))
    (σ : CompactType K n) :
    Module.Finite ℂ
      ((Submodule.span ℂ
        (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
          compactAction K n p.1 (operator K n p.2 f))).topologicalClosure ⊓
          compactTypeSubmodule σ : Submodule ℂ (DerivativeSmoothFunctions K n)) := by
  rw [generatedCompactType_inf_topologicalClosure_eq K n f hf hz σ]
  rw [inf_comm]
  exact generatedCompactTypeFiniteness K n f hf hz σ

/-- With actual compact-and-enveloping orbit density also supplied, each
compact-type intersection of the closed full group orbit span is finite. -/
theorem closedGroupOrbit_compactType_finite
    (h_density : CompactLieOrbitDensityStatement K n)
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f))
    (σ : CompactType K n) :
    Module.Finite ℂ
      ((Submodule.span ℂ
        (Set.range fun g : InfiniteAdelicGL K n =>
          rightAction K n g f)).topologicalClosure ⊓ compactTypeSubmodule σ :
          Submodule ℂ (DerivativeSmoothFunctions K n)) := by
  let M : Submodule ℂ (DerivativeSmoothFunctions K n) :=
    Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        compactAction K n p.1 (operator K n p.2 f))
  let N : Submodule ℂ (DerivativeSmoothFunctions K n) :=
    Submodule.span ℂ
      (Set.range fun g : InfiniteAdelicGL K n => rightAction K n g f)
  have hf_smooth : Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype)
      (toSmooth K n f) :=
    Langlands.FiniteVectors.IsFiniteVector.map
      (compactActionEquiv K n).toIntertwiningMap hf
  have h_joint : IsJointFinite K n (toSmooth K n f) :=
    separateJointFinite K n _ hz (compactGroupFiniteDifferential K n _ hf_smooth)
  have h_le : N ≤ M.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact h_density f h_joint g
  have h_closure : N.topologicalClosure ≤ M.topologicalClosure :=
    N.topologicalClosure_minimal h_le M.isClosed_topologicalClosure
  have : Module.Finite ℂ
      (M.topologicalClosure ⊓ compactTypeSubmodule σ :
        Submodule ℂ (DerivativeSmoothFunctions K n)) :=
    generatedCompactType_topologicalClosure_finite K n f hf hz σ
  exact Submodule.finiteDimensional_of_le (inf_le_inf_right _ h_closure)

end Langlands.Global.ArchimedeanGL
