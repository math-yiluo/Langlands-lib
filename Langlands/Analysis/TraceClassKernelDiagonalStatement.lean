import Langlands.Analysis.OperatorTrace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The trace of a trace-class integral operator as a diagonal integral

Brislawn, *Traceable integral kernels on countably generated measure spaces*,
Pacific J. Math. 150 (1991), Corollary 3.2 (printed p. 237).
The integrability conclusion follows from Theorem 3.1 (printed p. 235)
and the diagonal identification of Theorem 2.4 (printed p. 234).
-/

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

open MeasureTheory

universe u

/-- Let `μ` be a σ-finite Borel measure on a second-countable space `X`, and let `T` be a
trace-class operator on `L²(X, μ)` given by a kernel `K ∈ L²(X × X, μ × μ)`: for every
`φ ∈ L²(X, μ)`, `(T φ)(x) = ∫ K(x, y) φ(y) dμ(y)` for `μ`-almost every `x`. If `K` is
continuous at `(x, x)` for `μ`-almost every `x`, then `x ↦ K(x, x)` is integrable and the
trace of `T` is `∫ K(x, x) dμ(x)`. -/
def TraceClassContinuousKernelDiagonalStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SigmaFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (K : X → X → ℂ),
    IsTraceClass T →
    MemLp (Function.uncurry K) 2 (μ.prod μ) →
    (∀ φ : Lp ℂ 2 μ, (T φ : X → ℂ) =ᵐ[μ] fun x => ∫ y, K x y * φ y ∂μ) →
    (∀ᵐ x ∂μ, ContinuousAt (Function.uncurry K) (x, x)) →
    Integrable (fun x => K x x) μ ∧ operatorTrace T = ∫ x, K x x ∂μ

end Langlands.Analysis.OperatorIdeals
