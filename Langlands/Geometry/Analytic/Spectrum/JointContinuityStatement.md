# Joint continuity of spectrum evaluation and bounded pullback

Author: Worker 36.

This pair states three derived targets for the existing concrete
`BanachSpectrum`. Its points are normalized multiplicative ring seminorms
bounded above by the given norm. Its topology is pointwise convergence of
these seminorms. The algebra carries its norm topology throughout.
`JointContinuityStatement` is the conjunction of the following three
propositions. This file supplies statements, not their Lean proofs.

`UniformEvaluationBoundStatement` says that for every normed commutative
ring `A`, every spectrum point `x`, and all `a, b : A`,

```text
|x(a) - x(b)| ≤ ‖a - b‖.
```

The constant is one and is independent of `x`. No bound on the norm of a
family of ring maps is involved.

`JointEvaluationContinuityStatement` says that
`(x, a) ↦ x(a)` is continuous from `BanachSpectrum A × A` to the real
numbers, with the product topology. This is stronger than continuity in
the spectrum variable for a fixed algebra element, which is already
implemented by `BanachSpectrum.evaluation`.

`ParametricPullbackContinuityStatement` quantifies over normed commutative
rings `A` and `B`, an arbitrary topological parameter space `T`, and a
function `f : T → BoundedRingHom A B`. Its hypothesis is that for every
fixed `a : A`, the map `t ↦ f(t)(a)` is continuous into the normed ring
`B`. Its conclusion is continuity of

```text
(t, x) ↦ BanachSpectrum.comap (f t) x
```

from `T × BanachSpectrum B` to `BanachSpectrum A`. Every `f t` has its own
positive linear norm bound as part of `BoundedRingHom`. The statement
requires neither a common bound nor any topology on the type of bounded
ring maps. The ring and parameter universes are independent.

These targets require neither completeness nor an ultrametric norm,
nontrivial valuation, a scalar field, or a nonempty spectrum. In
particular they also cover degenerate rings and empty spectra.

The proposed proof route is internal. The triangle inequality for a
seminorm gives `|x(a) - x(b)| ≤ x(a-b)`, and `x.le_norm` gives the first
target. Near a fixed `(x₀,a₀)`, split the evaluation difference through
`x(a₀)`. The first bound controls the varying algebra element uniformly
in `x`; the existing continuous evaluation at `a₀` controls the other
term. Finally, for each fixed `a`, the coordinate of parametric pullback
is `x(f(t)(a))`. Joint evaluation and the stated orbit-continuity
hypothesis give continuity of this coordinate, and the induced spectrum
topology gives the last target. This paragraph describes a proof route,
not a completed Lean proof.

The source context is Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), printed/PDF p. 4: Definition 1.2.3,
Exercise 1.2.4 and Definition 1.2.5. The source supplies bounded
multiplicative seminorms, their constant-one bound, and the evaluation
topology. The three joint-continuity targets are derived consequences,
not separately attributed numbered claims. Registered source:
`berkovich-2009-trieste-analytic-spaces`; PDF SHA256:
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

This is topological infrastructure for later continuous actions on
concrete affinoid spectra. It introduces no analytic automorphism
topology, continuous analytic group action, structure sheaf, analytic
atlas, or equivariant etale site.
