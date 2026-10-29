import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Constructions

/-!
# Finite operator expansion of a smooth representation of `Fˣ`

The remarks preceding JPS (1979), Lemma (2.2.1), printed p.181: a smooth
representation of `Fˣ` whose operators span a finite-dimensional space expands
into finitely many finite functions times operators in the span of the actual
operators `σ(b)` with `|b| ≤ 1`, and these bounded operators span the whole
operator space. This is a proposition definition, not a proof.
-/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- JPS (1979), p.181, remarks before Lemma (2.2.1): let `σ` be a smooth complex
representation of `Fˣ` whose operators `σ(a)` span a finite-dimensional space `S`
of endomorphisms. Then `S` is spanned by the operators `σ(b)` with normalized
absolute value `|b| ≤ 1`, and there are a finite set `Y` of continuous functions
on `Fˣ` with finite-dimensional left-translate span and operators `A η` in that
bounded span such that `σ(b) = ∑ η ∈ Y, η(b) A η` for every unit `b`. -/
def FiniteOperatorExpansionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ F.Carrierˣ V),
      IsSmooth σ →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range σ)) →
      Submodule.span ℂ {B : Module.End ℂ V |
          ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧ σ b = B} =
        Submodule.span ℂ (Set.range σ) ∧
      ∃ (Y : Finset (F.Carrierˣ → ℂ)) (A : (F.Carrierˣ → ℂ) → Module.End ℂ V),
        (∀ η ∈ Y, Continuous η ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))) ∧
        (∀ η ∈ Y, A η ∈ Submodule.span ℂ {B : Module.End ℂ V |
          ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧ σ b = B}) ∧
        ∀ b : F.Carrierˣ, σ b = ∑ η ∈ Y, η b • A η

end Langlands
