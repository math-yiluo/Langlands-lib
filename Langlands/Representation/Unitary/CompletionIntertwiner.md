# Completed isometric embeddings induced by form-preserving intertwiners

This module extends an actual form-preserving intertwiner between two
algebraic unitarizable representations to an actual complex-linear isometry
between their Hilbert completions. It proves equivariance, injectivity,
norm and inner-product preservation, and that the image is a closed
invariant complex subspace of the target completion. It uses the published
`Langlands.Representation.Unitary.Completion` module without changing it.
Mathlib's `Mathlib.Analysis.Normed.Operator.Extend` supplies the completion
extension `LinearIsometry.completion`.

## Parameters

All declarations are in `Langlands.InvariantPositiveForm`. The common telescope is

```lean
universe uG uV uW
{G : Type uG} [Group G]
{V : Type uV} [AddCommGroup V] [Module ℂ V]
{W : Type uW} [AddCommGroup W] [Module ℂ W]
{ρ : Representation ℂ G V} {σ : Representation ℂ G W}
(b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ)
(f : ρ.IntertwiningMap σ)
(hf : ∀ v w, c.inner (f v) (f w) = b.inner v w)
```

The group, source carrier and target carrier have independent universes.
The only analytic input is the exact form-preservation equation `hf`. The
module assumes no topology on `G` and no continuity in the group variable.
It puts no norm or topology on `V` or `W`, and needs no irreducibility,
admissibility, smoothness or finite dimensionality. It does not assume that
`f` is injective, because `hf` and the definiteness of `b` imply it:
`injective_of_inner_map b c f hf : Function.Injective f` is proved in the
next section. If `f v = f w`, then `normedIntertwiner b c f hf` takes the same
value on `b.toNormedCarrier v` and `b.toNormedCarrier w`. A linear isometry
is injective, and `b.toNormedCarrier` is a linear equivalence, so `v = w`.

## Pulled-back forms

`inner_map_comap c f hf' v w` states, for an injective intertwiner
`hf' : Function.Injective f`,

```lean
c.inner (f v) (f w) = (c.comap f hf').inner v w
```

It holds by `rfl` from the published definition of `InvariantPositiveForm.comap`.
So a consumer can set `b := c.comap f hf'` and pass `c.inner_map_comap f hf'`,
or equally `fun _ _ => rfl`, as `hf`.

## The normed and completed isometries

`normedIntertwiner b c f hf : b.NormedCarrier →ₗᵢ[ℂ] c.NormedCarrier` is the
linear map `f`, transported between the form-dependent normed carriers by
`toNormedCarrier`. Mathlib's `LinearMap.isometryOfInner` turns it into a
linear isometry, since the inner products on these carriers are `b.inner` and
`c.inner` by definition and `hf` is exactly the required identity.
`normedIntertwiner_toNormedCarrier` evaluates it on `b.toNormedCarrier v` as
`c.toNormedCarrier (f v)`.

`completedIsometry b c f hf : b.HilbertCompletion →ₗᵢ[ℂ] c.HilbertCompletion`
is the extension `LinearIsometry.completion` of `normedIntertwiner` to the
actual uniform completions. `completedIsometry_toHilbert` proves

```lean
b.completedIsometry c f hf (b.toHilbert v) = c.toHilbert (f v)
```

from Mathlib's `LinearIsometry.completion_apply_coe`.

`completedIsometry_completedOperator` proves, for every `g : G` and
`x : b.HilbertCompletion`,

```lean
b.completedIsometry c f hf (b.completedOperator g x) =
  c.completedOperator g (b.completedIsometry c f hf x)
```

Both sides are continuous in `x`, so the equation holds on a closed set. By
the published `denseRange_toHilbert` it suffices to check it on `b.toHilbert v`.
There the evaluation laws `completedOperator_toHilbert`,
`completedIsometry_toHilbert` and the intertwining identity `f (ρ g v) = σ g (f v)`
reduce both sides to `c.toHilbert (σ g (f v))`.
`completedIsometry_completedRepresentation` is the same equation for
`completedRepresentation`, whose evaluation is `completedOperator` by definition.

Since `completedIsometry` is a linear isometry, Mathlib gives the remaining
laws. `completedIsometry_injective` states injectivity,
`norm_completedIsometry` states `‖e x‖ = ‖x‖`, and
`inner_completedIsometry` states `inner ℂ (e x) (e y) = inner ℂ x y`,
where `e` denotes `b.completedIsometry c f hf`.

## Continuous linear map and intertwiner

`completedContinuousLinearMap b c f hf : b.HilbertCompletion →L[ℂ] c.HilbertCompletion`
is the underlying continuous linear map, and
`completedContinuousLinearMap_apply` states that it evaluates as
`completedIsometry`.

`completedIntertwiner b c f hf :
b.completedRepresentation.IntertwiningMap c.completedRepresentation`
is the same linear map as a Mathlib intertwiner of the completed
representations, with intertwining identity
`completedIsometry_completedRepresentation`.
`completedIntertwiner_apply` states its evaluation, and
`continuous_completedIntertwiner` its continuity.

## The closed range

`isClosed_range_completedIsometry` proves that `Set.range e` is closed.
The source `b.HilbertCompletion` is a complete metric space, and Mathlib's
`Isometry.isClosedEmbedding` shows that an isometry from a complete space is
a closed embedding. No closedness, embedding or projection is assumed.
`isClosed_range_completedContinuousLinearMap` restates the same fact for
`completedContinuousLinearMap`.

`completedRange b c f hf : Subrepresentation c.completedRepresentation` is
Mathlib's `IntertwiningMap.range` of `completedIntertwiner`. Hence it is a
complex submodule of the target completion, stable under every operator
`c.completedRepresentation g`. The following laws describe it.

- `completedRange_toSubmodule`: its submodule is
  `LinearMap.range (completedIsometry b c f hf).toLinearMap`.
- `mem_completedRange`: `y` belongs to it exactly when `y = e x` for some `x`.
- `coe_completedRange`: its carrier set is `Set.range e`.
- `isClosed_completedRange`: its carrier set is closed in `c.HilbertCompletion`.
- `coe_completedRange_eq_closure`: its carrier set equals
  `closure (Set.range fun v : V => c.toHilbert (f v))`.

The last law is proved by two inclusions. Each `e x` lies in this closure:
the preimage of the closure under `e` is closed, and it contains the dense set
of vectors `b.toHilbert v`, since `e (b.toHilbert v) = c.toHilbert (f v)`.
Conversely, the range of `e` is closed and contains every `c.toHilbert (f v)`.

## Provenance and scope

This is an internal analytic construction derived from the published
`Langlands.Representation.Unitary.Basic` and
`Langlands.Representation.Unitary.Completion` modules. It is not a
transcription of a numbered literature result; the arguments above supply
its content. Mathlib provides the completion extension of linear
isometries, the inner-product form of isometries, closed embeddings from
complete spaces and the range subrepresentation of an intertwiner.

The module constructs neither the coefficient map into central L2, nor a
decomposition of central L2, nor an orthogonal projection onto the range.
It proves no smooth-vector recovery, irreducibility comparison or
genericity statement.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
with Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Author: Worker 380.
