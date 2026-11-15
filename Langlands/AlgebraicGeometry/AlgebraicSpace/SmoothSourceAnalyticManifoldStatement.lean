import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticStructure

/-!
# The analytic manifold structure on rational points of all smooth spaces

Conrad's Proposition 5.4, analytic-manifold assertion (printed p.15), with the
dimension allowed to vary from point to point.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Proposition 5.4, analytic-manifold assertion (printed p.15), for
smooth spaces of varying dimension: let `K` be a complete nontrivially normed
field. There is a varying-dimension analytic structure on the original rational
points of every smooth, quasi-separated, locally separated algebraic space over
`Spec K`, for the étale-chart topology, that is analytic, makes every morphism
an analytic map, makes every étale morphism a local analytic isomorphism, and
makes the coordinates of every affine space analytic in both directions. Any two
such structures are equivalent. -/
def SmoothSourceAnalyticManifoldStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K],
    (∃ Φ : DimensionAnalyticStructure K, Φ.IsAdmissible) ∧
      ∀ Φ Ψ : DimensionAnalyticStructure K,
        Φ.IsAdmissible → Ψ.IsAdmissible → Φ.Equivalent Ψ

end Langlands.AlgebraicGeometry.AlgebraicSpace
