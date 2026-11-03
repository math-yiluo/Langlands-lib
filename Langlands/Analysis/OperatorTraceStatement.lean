import Langlands.Analysis.OperatorTrace

namespace Langlands.Analysis.OperatorIdeals

universe u v w

/-- Absolute convergence and the supplied-basis formula for the chosen trace. -/
def OperatorTraceBasisStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (ι : Type v)
    (b : HilbertBasis ι ℂ E), IsTraceClass A →
      Summable (fun i => ‖inner ℂ (b i) (A (b i))‖) ∧
      operatorTrace A = traceIn b A

/-- The trace is complex linear on the trace-class domain. -/
def OperatorTraceLinearityStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E],
    operatorTrace (0 : E →L[ℂ] E) = 0 ∧
    (∀ (A D : E →L[ℂ] E), IsTraceClass A → IsTraceClass D →
      operatorTrace (A + D) = operatorTrace A + operatorTrace D) ∧
    (∀ (c : ℂ) (A : E →L[ℂ] E), IsTraceClass A →
      operatorTrace (c • A) = c * operatorTrace A)

/-- Bounded rectangular cyclicity, including membership of both endomorphisms. -/
def OperatorTraceCyclicityStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] E) (B : E →L[ℂ] F) (C : F →L[ℂ] E),
    IsTraceClass A →
      IsTraceClass ((B.comp A).comp C) ∧
      IsTraceClass (A.comp (C.comp B)) ∧
      operatorTrace ((B.comp A).comp C) = operatorTrace (A.comp (C.comp B))

/-- Supplied-basis identification, linearity and bounded rectangular cyclicity. -/
def OperatorTraceLawsStatement : Prop :=
  OperatorTraceBasisStatement.{u, w} ∧
  OperatorTraceLinearityStatement.{u} ∧
  OperatorTraceCyclicityStatement.{u, v}

end Langlands.Analysis.OperatorIdeals
