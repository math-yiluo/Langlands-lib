# The principle of meromorphic continuation

Module `Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement` states
Bernstein–Lapid's principle of meromorphic continuation as three proposition
definitions. It supplies no proof.

- `MeromorphicContinuationHolomorphicStatement`: the openness in part (1),
  and parts (2) and (3).
- `MeromorphicContinuationAnalyticComplementStatement`: the analyticity of the
  complement in part (1).
- `MeromorphicContinuationPrincipleStatement`: the conjunction of the two,
  which is the whole theorem.

The objects are those of `Langlands.Analysis.Meromorphic.AnalyticSystems`.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. Theorem 3.3
(Principle of meromorphic continuation) is on p.194 of the journal PDF in the
registered folder. Its setting is fixed at the start of §3 (p.192: `M` is a
complex analytic manifold) and in the Definition of §3.3 (p.194). Appendix A
(pp.230–231) proves it.

## Hypotheses

Both parts quantify over the same data, with five independent universes:

- `E` is a finite-dimensional complex normed space, and `M` is a manifold
  charted on `E` with `IsManifold 𝓘(ℂ, E) 1 M`. Its transition maps are
  complex differentiable, hence holomorphic, so `M` is a complex analytic
  manifold of dimension `dim E`. This is Mathlib's convention for complex
  manifolds (`Mathlib.Geometry.Manifold.Complex`). `ConnectedSpace M` says
  that `M` is connected and nonempty. The source assumes `M` connected, and
  nonemptiness also follows from the third hypothesis below.
- `V` is a complex Hausdorff locally convex topological vector space: a
  topological additive group with continuous complex scalar multiplication,
  `T2Space`, and `LocallyConvexSpace ℝ V` for a real structure compatible
  with the complex one (`IsScalarTower ℝ ℂ V`). Local convexity does not
  depend on the scalar field. Mathlib states it over an ordered field, hence
  over `ℝ`.
- `ι` is an arbitrary index type, possibly infinite, and every `F i` is a
  complex Hausdorff locally convex topological vector space in the same
  sense.
- `μ i : M → V →L[ℂ] F i` and `c i : M → F i` form the system
  `Ξ(s) : μ i s v = c i s (i ∈ ι)` on `v ∈ V`, as in Definition (1) of §3.3.

The three assumptions of Theorem 3.3 are:

1. `IsAnalyticSystem 𝓘(ℂ, E) μ c`: `Ξ` is an analytic family of systems.
2. `IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c)`: `Ξ` is locally of
   finite type, that is, its solution sets are (Definition (4) of §3.3).
3. `(interior (uniqueSolutionLocus μ c)).Nonempty`: the interior of `M_unq`
   is nonempty. Connectedness of `M` is the instance above.

## Conclusions

`MeromorphicContinuationHolomorphicStatement` concludes that there is
`v : M → V` such that

- `systemSolutions μ c s = {v s}` for every `s ∈ M_unq`. So `v` is the
  source's function `v(s)`, the unique solution, on `M_unq`. Its values off
  `M_unq` are arbitrary and play no role below.
- `M_unq` is open (the first half of part (1)).
- `IsHolomorphicOn 𝓘(ℂ, E) v M_unq`: `v` is holomorphic on `M_unq` (part (2)).
- `IsMeromorphicOn 𝓘(ℂ, E) v M_unq`: `v` is meromorphic on `M` (part (3)).
  The definition of meromorphy requires its domain of holomorphy to be open
  and dense, so this conclusion includes density of `M_unq`. In the source,
  density follows from part (1): the complement of `M_unq` is an analytic
  subset of the connected manifold `M` and is not all of `M`.

`MeromorphicContinuationAnalyticComplementStatement` concludes that the
complement of `M_unq` is an analytic subset of `M` in the sense of
`IsAnalyticSubset`: locally the common zeros of finitely many holomorphic
functions (the second half of part (1)).

## Why two parts

The proof of Appendix A shows that near each point, `M_unq` is a union of
nonvanishing loci of holomorphic determinants (Cramer's rule). This gives
openness, holomorphy and meromorphy directly. The complement is then locally
the common zero set of a possibly infinite family of holomorphic functions.
Finitely many of them suffice by the Noetherian property of rings of
convergent power series, which is a separate and deeper input. The split
lets parts (2) and (3), which are what the continuation of Eisenstein series
uses, be proved and used before that input is available. The conjunction
`MeromorphicContinuationPrincipleStatement` is the complete theorem.

## Scope

No Fredholm criterion (the Lemma of §3.4 and Corollary 3.4), Eisenstein series,
intertwining operator or function space of uniform moderate growth is
stated here.
