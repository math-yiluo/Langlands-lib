# Hilbert completion of an invariant positive form

This module constructs the actual complete Hilbert realization of an algebraic
complex representation with the published invariant positive definite form.
It proves strong continuity when the original representation is smooth.
It uses the existing `Langlands.InvariantPositiveForm` and `Langlands.IsSmooth`
without changing either definition.

## Parameters and construction

All declarations are in `Langlands.InvariantPositiveForm`. The common telescope is

```lean
universe uG uV
{G : Type uG} [Group G]
{V : Type uV} [AddCommGroup V] [Module ℂ V]
{ρ : Representation ℂ G V} (b : InvariantPositiveForm ρ)
```

The group and carrier universes are independent. Construction of the complete
space and its action requires no topology on either original carrier.
`NormedCarrier b : Type uV` is a separate type synonym of `V`. Its additive and
complex module structures are transported from `V`. Its norm is determined by
the given positive form:

```text
‖toNormedCarrier b v‖ = sqrt (Re (b.inner v v)).
```

The proof uses Mathlib's `InnerProductSpace.Core.toNormedAddCommGroup` and
`InnerProductSpace.ofCore`. The existing form supplies Hermitian symmetry,
sesquilinearity, nonnegativity and definiteness. In particular, this produces
a norm, rather than only a seminorm. `toNormedCarrier` is the complex-linear
equivalence identifying the algebraic carrier with this copy;
`inner_toNormedCarrier` and `norm_toNormedCarrier` give the exact formulas.
No norm or topology is installed as an instance on the incoming `V`.

`HilbertCompletion b : Type uV` is literally
`UniformSpace.Completion (NormedCarrier b)`. Mathlib supplies its
`NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace` instances.
`toHilbert b : V →ₗ[ℂ] HilbertCompletion b` composes `toNormedCarrier`
with Mathlib's canonical linear isometry into the completion.

`toHilbert_injective` follows from the two component injections.
`denseRange_toHilbert` combines the surjectivity of `toNormedCarrier` with the
dense range of the canonical completion map. `inner_toHilbert` states exactly

```lean
inner ℂ (b.toHilbert v) (b.toHilbert w) = b.inner v w
```

by Mathlib's `UniformSpace.Completion.inner_coe`.
`norm_toHilbert` gives the same square-root formula for the embedding's norm.
None of these results assumes `Nontrivial V`; the zero vector space is included.

## Extension of the representation

`normedOperator b g : b.NormedCarrier →ₗᵢ[ℂ] b.NormedCarrier`
is the actual operator `ρ g`, transported along `toNormedCarrier`.
The supplied invariance identity `b.invariant` makes this a linear isometry,
using Mathlib's `LinearMap.isometryOfInner`.

`completedLinearMap b g : b.HilbertCompletion →L[ℂ] b.HilbertCompletion`
is `ContinuousLinearMap.completion` of this isometry's continuous linear map.
Thus it is constructed by extension from the original operator.
`completedLinearMap_toHilbert` proves its evaluation on every embedded vector:

```lean
b.completedLinearMap g (b.toHilbert v) = b.toHilbert (ρ g v)
```

The identity and multiplication laws, `completedLinearMap_one` and
`completedLinearMap_mul`, follow by equality on this dense range, since both
sides are continuous. Norm preservation follows by extending a closed equality
from that same dense range, using the explicit norm formula and `b.invariant`.

`completedOperator b g : b.HilbertCompletion ≃ₗᵢ[ℂ] b.HilbertCompletion`
packages this extension as a complex-linear isometric equivalence. Its inverse
function is the extension at `g⁻¹`; the representation laws prove both inverse
identities. `completedOperator_symm` identifies its inverse equivalence with
`completedOperator b g⁻¹`. The usual continuity and inverse evaluation laws of
`LinearIsometryEquiv` therefore apply. `completedOperator_toHilbert`,
`completedOperator_norm` and `completedOperator_inner` give equivariance,
norm preservation and inner-product preservation.

`completedRepresentation b : Representation ℂ G b.HilbertCompletion` is the
resulting algebraic representation on the actual complete space.
`completedRepresentation_apply` identifies its evaluation with
`completedOperator`. It has the standard monoid-homomorphism identity and
multiplication laws. `completedRepresentation_toHilbert`,
`completedRepresentation_norm` and `completedRepresentation_inner` expose
the corresponding embedding and preservation identities for this interface.

## Strong continuity

Only `continuous_completedOrbit` adds

```lean
[TopologicalSpace G] [IsTopologicalGroup G]
(hρ : IsSmooth ρ) (x : b.HilbertCompletion)
```

and concludes

```lean
Continuous (fun g : G => b.completedRepresentation g x).
```

The proof works at an arbitrary `g₀` in the given topology on `G`. For
`ε > 0`, choose `v : V` with `dist x (b.toHilbert v) < ε / 2`, using
`denseRange_toHilbert`. Published smoothness gives an open subgroup `K`
fixing `v`. The set of `g` with `g₀⁻¹ * g ∈ K` is a neighborhood of `g₀`
by continuity of group multiplication. On this neighborhood, the
representation law and the fixed-vector identity imply that `g` and `g₀`
act equally on `b.toHilbert v`. The triangle inequality and the isometry of
each operator bound the distance between their values at `x` by
`2 * dist x (b.toHilbert v) < ε`. This proves continuity of every orbit.

There is no operator-norm-continuity assertion. No local compactness, compact
open subgroup basis, finite dimensionality, admissibility, irreducibility,
chosen completion or analytic comparison premise is required.

## Provenance and scope

This is an internal analytic construction derived from the published
`Langlands.Representation.Unitary.Basic` form and
`Langlands.Representation.Smooth.Definitions` open-stabilizer predicate.
The implementation and the continuity argument above supply its mathematical
content; there is no claim to translate a separately numbered literature
theorem. Mathlib provides the positive-core norm construction, actual uniform
completion, extension of continuous linear maps, and inner-product identities
for linear isometries.

Density does not here assert recovery of all smooth vectors or any equivalence
between algebraic and closed irreducibility. Smooth-vector recovery,
irreducibility comparisons, square-integrability and its L2 comparison,
mirabolic restriction, induction irreducibility and genericity remain separate
theorem obligations.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
with Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Author: Worker 108.
