# Weak integration tested by the smooth contragredient

This internal construction defines weak integration into an algebraic complex
representation. The namespace is
`Langlands.HarmonicAnalysis.SmoothWeakIntegral`. The measurable domain `X`,
group `G`, and complex carriers `V` and `W` have independent universes. The
carriers have only additive commutative groups and complex module structures;
no topology, norm, completeness, finite dimension, or measurable structure is
imposed on them.

## Relation and actual domain

For a representation `ρ`, a measure `μ`, a function `f : X → V`, and a vector
`v : V`, `HasIntegral ρ μ f v` means that for every `ℓ : SmoothDual ρ`, the
complex function `x ↦ ℓ.val (f x)` is Bochner integrable and

\[
\int_X \ell(f(x))\,d\mu(x)=\ell(v).
\]

The tests are exactly the published smooth contragredient carrier, not all
algebraic functionals. The integrals are Mathlib's genuine scalar Bochner
integrals, and their integrability is explicitly required. No arbitrary
scalar data or representation-data field supplies the values or existence.
`Integrable ρ μ f` additionally requires a representing vector in `V`.
Existence of all scalar integrals alone is not asserted to imply this property.
These two predicates need only a topology on the group; they do not require
ambient smoothness or the topological-group axiom.

`hasIntegral_zero`, `HasIntegral.add`, and `HasIntegral.smul` follow from
linearity of each test functional and the scalar integral. They construct
`integrableSubmodule ρ μ`, the submodule of actual functions admitting a
representing vector. This is a submodule of `X → V`, not a quotient by almost
everywhere equality. No sigma-finiteness of the measure is assumed.

## Uniqueness and the linear integral

For a topological group, assume `hρ : IsSmooth ρ` and the explicit cofinality
hypothesis that every open subgroup contains a compact open subgroup.
`HasIntegral.unique` uses the published
`smoothBidual_injective_of_compact_cofinal`: equality of all scalar tests
gives equality of the smooth bidual evaluations, and injectivity gives equality
of the vectors. Admissibility is not needed.

`integralLinear hcofinal hρ` chooses a representing vector from the existence
proof carried by an element of `integrableSubmodule ρ μ`. Uniqueness and the
already proved addition and scalar laws make this choice into a complex linear
map. There is no chosen default value for nonintegrable functions.
`integralLinear_spec` proves its weak-integral relation;
`integralLinear_eq` identifies it with any explicit representing vector;
`integralLinear_eval` identifies each smooth-functional evaluation with the
scalar Bochner integral.

## Naturality

For an actual representation intertwiner `T : ρ.IntertwiningMap σ`,
`HasIntegral.map` tests against `contragredientMap T ℓ`. Its evaluation is
by definition `ℓ.val (T v)`, so the original scalar integrability and integral
equation give the transported ones directly. This relational result needs the
topological-group structure required by smooth dual pullback, but neither
representation needs to be smooth and no cofinality is required.
`mapIntegrable T` bundles postcomposition as a linear map between the actual
integrable submodules. `integralLinear_map` proves its commutation with the
linear integrals when both representations are smooth and the common group
has the displayed compact-open cofinality property. The target carrier has
its own independent universe. No continuity of an algebraic intertwiner is
required.

## Finite simple functions and compact locally constant functions

For `f : SimpleFunc X V` with `f.FinMeasSupp μ`,
`hasIntegral_simpleFunc` identifies its weak integral with the published
`AlgebraicIntegral.integral μ f`, the finite fiber sum. The proof maps `f`
through each smooth functional; the resulting complex simple function has
finite-measure support and is integrable. The published scalar Bochner
comparison and commutation of the finite sum with linear maps then give the
evaluation identity. This relation requires no uniqueness hypotheses.
`integralLinear_simpleFunc` also identifies the chosen linear integral under
the smoothness and cofinality assumptions.

`hasIntegral_compactlySupported` uses the published
`compactlySupportedSimpleFunc` and
`compactlySupportedSimpleFunc_finMeasSupp` for a locally constant function
with compact topological support. Here the domain additionally has a topology,
open sets are measurable, and the measure is finite on compact sets. The
conversion has exactly the original values, so its algebraic integral gives
a weak integral of the original function. `integrable_compactlySupported`
records membership in the actual integrable domain. No global measure
finiteness or sigma-finiteness is required.

## Provenance and scope

This is an internal foundational construction, derived from the current
Library's `AlgebraicIntegral`, `AlgebraicIntegrand`, and smooth-contragredient
separation results, together with scalar integration in the pinned Mathlib.
Its intrinsic proofs are described above; no new assertion is attributed to
an external paper. The existing smooth-dual separation theorem is imported,
not reproved or assumed as a new axiom.

For the intended later Shahidi intertwining integrals, convergence and
representability of the noncompact integrand remain separate statement and
proof obligations. Rational continuation also remains separate. This module
neither constructs nor assumes Shahidi's operator `A_s`, and it supplies no
analytic existence theorem for such an integrand.
