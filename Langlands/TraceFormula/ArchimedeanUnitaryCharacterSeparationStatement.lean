import Langlands.Global.ArchimedeanConvolution
import Langlands.Representation.Archimedean.SmoothVectors
import Langlands.Analysis.OperatorTrace

/-!
# Separation of archimedean characters of irreducible unitary representations

Let `F` be a number field and `G∞ = GL_n(F ⊗ ℝ)`, the group `InfiniteAdelicGL F n` of
invertible matrices over `InfiniteAdeleRing F`, with a left Haar measure `μ` and the test
functions `ArchimedeanGL.SmoothCompactKernel F n` (smooth compactly supported functions).
For a unitary representation `σ` of `G∞` on a complex Hilbert space and a test function `f`,
the integrated operator `σ(f)` is determined by `σ(f) x = ∫ f(g) σ(g) x dμ(g)`.

This file states, without proof:

* `ArchimedeanUnitaryTraceClassStatement`: for an irreducible unitary representation `σ`
  and every test function `f`, the integrated operator `σ(f)` exists and is of trace class.
* `ArchimedeanUnitaryCharacterSeparationStatement`: if a family of characters of irreducible
  unitary representations `σ i`, weighted by complex numbers `c i`, sums for every test
  function to `c₀` times the character of an irreducible unitary representation `π`, then
  the coefficients `c i` over the indices with `σ i` unitarily equivalent to `π` sum to `c₀`;
  in particular some `σ i` is unitarily equivalent to `π` when `c₀ ≠ 0`.

The paired Markdown explains the notation, the hypotheses, the sources and why the
statements hold.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

universe uF uι uH uE

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Analysis.OperatorIdeals

namespace ArchimedeanUnitary

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A unitary representation of `GL_n(F ⊗ ℝ)`: the action map `G∞ × H → H` is jointly
continuous and every operator `σ g` preserves the inner product. -/
def IsUnitaryRepresentation (σ : InfiniteAdelicGL F n →* (H →L[ℂ] H)) : Prop :=
  Langlands.Archimedean.IsContinuousRepresentation σ ∧
    ∀ (g : InfiniteAdelicGL F n) (x y : H), ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ

/-- An irreducible unitary representation: a unitary representation on a nonzero space
whose only closed invariant subspaces are `⊥` and `⊤`. -/
def IsIrreducibleUnitaryRepresentation (σ : InfiniteAdelicGL F n →* (H →L[ℂ] H)) : Prop :=
  IsUnitaryRepresentation σ ∧ Langlands.Archimedean.IsTopologicallyIrreducible σ

/-- The bounded operator `A` is the integrated operator `σ(f) = ∫ f(g) σ(g) dμ(g)`, taken
vectorwise as Bochner integrals: `A x = ∫ f(g) • σ(g) x dμ(g)` for every vector `x`. -/
def IsIntegratedOperator [MeasurableSpace (InfiniteAdelicGL F n)]
    (μ : Measure (InfiniteAdelicGL F n)) (σ : InfiniteAdelicGL F n →* (H →L[ℂ] H))
    (f : SmoothCompactKernel F n) (A : H →L[ℂ] H) : Prop :=
  ∀ x : H, A x = ∫ g, f.val.val g • σ g x ∂μ

/-- Unitary equivalence: a surjective linear isometry `e : H ≃ₗᵢ[ℂ] E` that intertwines the
two actions, `e (σ g x) = τ g (e x)`. -/
def UnitarilyEquivalent (σ : InfiniteAdelicGL F n →* (H →L[ℂ] H))
    (τ : InfiniteAdelicGL F n →* (E →L[ℂ] E)) : Prop :=
  ∃ e : H ≃ₗᵢ[ℂ] E, ∀ (g : InfiniteAdelicGL F n) (x : H), e (σ g x) = τ g (e x)

end ArchimedeanUnitary

open ArchimedeanUnitary

/-- Harish-Chandra's trace-class theorem for `GL_n(F ⊗ ℝ)`: for every number field `F`,
every `n`, every left Haar measure `μ` and every irreducible unitary representation `π`
on a complex Hilbert space, each smooth compactly supported test function `f` has an
integrated operator `π(f) = ∫ f(g) π(g) dμ(g)`, and it is of trace class. -/
def ArchimedeanUnitaryTraceClassStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] (n : ℕ)
    [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
    (μ : Measure (InfiniteAdelicGL F n)) [μ.IsHaarMeasure]
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : InfiniteAdelicGL F n →* (E →L[ℂ] E)),
    IsIrreducibleUnitaryRepresentation π →
    ∀ f : SmoothCompactKernel F n,
      ∃ B : E →L[ℂ] E, IsIntegratedOperator μ π f B ∧ IsTraceClass B

/-- Separation of archimedean characters in summable families. Let `σ i` (for `i : ι`) and
`π` be irreducible unitary representations of `GL_n(F ⊗ ℝ)` with integrated operators
`A i f` and `B f`, and let `c : ι → ℂ` and `c₀ : ℂ`. If for every test function `f` the
family `c i * tr (A i f)` has (unconditional, equivalently absolutely convergent) sum
`c₀ * tr (B f)`, then the `c i` over the indices `i` with `σ i` unitarily equivalent to `π`
have sum `c₀`; if moreover `c₀ ≠ 0`, some `σ i` is unitarily equivalent to `π`. -/
def ArchimedeanUnitaryCharacterSeparationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] (n : ℕ)
    [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
    (μ : Measure (InfiniteAdelicGL F n)) [μ.IsHaarMeasure]
    (ι : Type uι) (H : ι → Type uH) [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
    (σ : (i : ι) → InfiniteAdelicGL F n →* (H i →L[ℂ] H i))
    (A : (i : ι) → SmoothCompactKernel F n → (H i →L[ℂ] H i))
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : InfiniteAdelicGL F n →* (E →L[ℂ] E)) (B : SmoothCompactKernel F n → (E →L[ℂ] E))
    (c : ι → ℂ) (c₀ : ℂ),
    (∀ i, IsIrreducibleUnitaryRepresentation (σ i)) →
    (∀ i f, IsIntegratedOperator μ (σ i) f (A i f)) →
    IsIrreducibleUnitaryRepresentation π →
    (∀ f, IsIntegratedOperator μ π f (B f)) →
    (∀ f, HasSum (fun i => c i * operatorTrace (A i f)) (c₀ * operatorTrace (B f))) →
    HasSum (fun i : {i : ι // UnitarilyEquivalent (σ i) π} => c i.val) c₀ ∧
      (c₀ ≠ 0 → ∃ i, UnitarilyEquivalent (σ i) π)

end Langlands.TraceFormula
