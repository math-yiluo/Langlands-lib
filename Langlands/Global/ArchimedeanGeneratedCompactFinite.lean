import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Global.ArchimedeanAdjointCoefficientsProof
import Langlands.Global.ArchimedeanCompactDifferentialGeneratedModule
import Langlands.Representation.FiniteVectors

/-! # Compact finiteness of the actual compact-and-enveloping span -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions
open scoped BigOperators

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Alias for the published actual compact-and-enveloping span. -/
abbrev generatedCompactDifferentialSpan (f : DerivativeSmoothFunctions K n) :
    Submodule ℂ (DerivativeSmoothFunctions K n) :=
  compactDifferentialGeneratedSpan K n f

/-- Published enveloping covariance transported to the derivative topology. -/
theorem compactAction_operator_covariance
    (k : standardInfiniteCompact K n) (a : EnvelopingAlgebra K n)
    (f : DerivativeSmoothFunctions K n) :
    compactAction K n k (operator K n a f) =
      operator K n (envelopingConjugation K n k.val a)
        (compactAction K n k f) := by
  simpa only [enveloping_smul_eq_operator] using
    compactAction_enveloping_smul K n k a f

private theorem operator_sum_smul {m : ℕ}
    (b : Fin m → EnvelopingAlgebra K n) (c : Fin m → ℂ)
    (f : DerivativeSmoothFunctions K n) :
    operator K n (∑ i, c i • b i) f =
      ∑ i, c i • operator K n (b i) f := by
  apply (toSmooth K n).injective
  simp only [toSmooth_operator, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply]

/-- Actual enveloping derivatives preserve compact finiteness. -/
theorem compactFinite_operator (a : EnvelopingAlgebra K n)
    {f : DerivativeSmoothFunctions K n}
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    Langlands.FiniteVectors.IsFiniteVector (compactAction K n) (operator K n a f) := by
  classical
  obtain ⟨m, b, c, hc⟩ := envelopingConjugationCoefficients K n a
  let O := Langlands.FiniteVectors.orbitSpan (compactAction K n) f
  have : Module.Finite ℂ O := hf
  let T : Submodule ℂ (DerivativeSmoothFunctions K n) :=
    ⨆ i : Fin m, O.map (operator K n (b i))
  have : Module.Finite ℂ T := by
    dsimp [T]
    infer_instance
  apply Submodule.finiteDimensional_of_le (S₂ := T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change compactAction K n k (operator K n a f) ∈ T
  rw [compactAction_operator_covariance, hc k.val, operator_sum_smul]
  apply Submodule.sum_mem
  intro i _
  apply T.smul_mem
  apply (le_iSup (fun j : Fin m => O.map (operator K n (b j))) i)
  exact ⟨compactAction K n k f,
    Langlands.FiniteVectors.action_mem_orbitSpan (compactAction K n) k f, rfl⟩

/-- Every vector in the actual algebraic compact-and-enveloping span is
compact-finite when its generator is compact-finite. -/
theorem generatedCompactDifferentialSpan_compactFinite
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    ∀ x, x ∈ Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        compactAction K n p.1 (operator K n p.2 f)) →
      Langlands.FiniteVectors.IsFiniteVector (compactAction K n) x := by
  change Submodule.span ℂ _ ≤
    (Langlands.FiniteVectors.subrepresentation (compactAction K n)).toSubmodule
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨k, a⟩, rfl⟩
  exact (compactFinite_operator K n a hf).action k

/-- The actual algebraic compact-and-enveloping span is compact-invariant. -/
theorem compactAction_mem_generatedCompactDifferentialSpan
    (f : DerivativeSmoothFunctions K n) (k : standardInfiniteCompact K n)
    {x : DerivativeSmoothFunctions K n}
    (hx : x ∈ Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        compactAction K n p.1 (operator K n p.2 f))) :
    compactAction K n k x ∈ Submodule.span ℂ
      (Set.range fun p : standardInfiniteCompact K n × EnvelopingAlgebra K n =>
        compactAction K n p.1 (operator K n p.2 f)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨l, a⟩, rfl⟩ := hy
    apply Submodule.subset_span
    exact ⟨(k * l, a), by simp only [map_mul, Module.End.mul_apply]⟩
  | zero => simp
  | add y z hy hz ihy ihz =>
    simpa only [map_add] using Submodule.add_mem _ ihy ihz
  | smul c y hy ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

end Langlands.Global.ArchimedeanGL
