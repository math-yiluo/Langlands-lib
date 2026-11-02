import Langlands.Algebra.SeparableTensor
import Mathlib.FieldTheory.PrimitiveElement

/-! # Tensor decomposition of a finite separable field extension -/

universe u v w

namespace Langlands.Algebra.SeparableTensor

/-- Over a field in which all minimal polynomials split, a finite separable extension
decomposes by evaluating at its embeddings. -/
def EmbeddingEvaluationStatement : Prop :=
  ∀ (k : Type u) (K : Type v) (Ω : Type w) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K],
    (∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits) →
      Function.Bijective (embeddingEvaluation k K Ω)

end Langlands.Algebra.SeparableTensor
