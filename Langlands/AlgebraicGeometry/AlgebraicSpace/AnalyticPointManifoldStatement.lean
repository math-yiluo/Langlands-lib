import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticPointManifold

/-!
# The analytic manifold structure on rational points of smooth algebraic spaces

Conrad's Proposition 5.4, analytic-manifold assertion (printed p.15): over a complete field,
the rational points of smooth algebraic spaces carry a unique functorial analytic manifold
structure that agrees with the scheme case and carries étale maps to analytic local
isomorphisms.
-/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Proposition 5.4, analytic-manifold assertion (printed p.15): let `K` be a complete
nontrivially normed field. There is a family of `K`-analytic manifold structures on the rational
points of the smooth, quasi-separated, locally separated algebraic spaces of pure relative
dimension `n` over `Spec K` (for every `n`), for the étale-chart topology, such that morphisms
induce analytic maps, étale morphisms induce analytic local isomorphisms, and on affine `n`-space
the coordinates are an analytic diffeomorphism onto `Kⁿ`. Any two such families agree. -/
def AnalyticPointManifoldStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K],
    (∃ σ : AnalyticPointStructure K, σ.IsAdmissible) ∧
      ∀ σ τ : AnalyticPointStructure K, σ.IsAdmissible → τ.IsAdmissible → σ.Equivalent τ

end Langlands.AlgebraicGeometry.AlgebraicSpace
