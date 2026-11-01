# Product-measure row splitting for the first-block Laurent calculation

Worker 1191 implements the measure and integration interfaces specified by
Worker 1037 for the first-block JPSS Laurent proof.
These are derived results about the published
`rectangularMeasure` and `HarmonicAnalysis.rowMeasure`, using the supplied scalar
Haar measure throughout. They do not assert the full first-block identity or
establish convergence of its representation-theoretic integrands.

The measurable equivalence `rowSplitEquiv` separates the last row of an
`(m + 1)` by `a` matrix, returning that row first and the remaining `m` rows
second. Its inverse is exactly the displayed `Fin.snoc` lambda; this module
introduces no `rowSnoc` constant. The construction specializes Mathlib's
`MeasurableEquiv.piFinSuccAbove` at `Fin.last m`.
`measurePreserving_rowSplitEquiv` and `measurePreserving_rowSnoc` prove that the
split and its inverse preserve the corresponding finite product measures.
The only scalar-space assumptions needed are an additive group, topology,
measurable space, and sigma-finiteness of the supplied Haar measure.

`integral_rectangular_rowSnoc` assumes joint almost everywhere strong
measurability of a complex function `H Z q` and finiteness of its iterated
extended-norm integral. Tonelli gives integrability on the rectangle times the
parameter space. The measure-preserving split, its product with the identity,
and product associativity give integrability on row times remaining rectangle
times parameter. Almost every row then has an integrable inner product
function, so Fubini exchanges the remaining rectangle and parameter integrals.
The theorem proves integrability of the resulting row function and the exact
identity with order `row`, `parameter`, `remaining rectangle`.
The parameter measure is any s-finite measure; zero-dimensional rectangles
and row spaces are included.

`integral_mul_integral_swap` uses the jointly almost everywhere strongly
measurable kernel `Kf x q`, with pointwise norm at most one, and integrable
functions `A` and `Φ`. The total integrand
`Φ x * (Kf x q * A q)` is dominated in norm by the integrable product
`Φ x * A q`. Fubini and commutativity of complex multiplication give
the stated interchange with `A q` outside the inner integral, as well as
integrability of the original outer function. Both measures are s-finite.

`rectangularMeasure_entries_pow` proves, for every scalar set `S`, that the
mass of the matrices with all entries in `S` is
`ν.measure S ^ (j * t)`. It applies the finite-product rectangle formula
twice and combines the powers. No measurability assumption on `S` is required
by that Mathlib formula. `rectangularMeasure_entries_swap` applies commutativity
of `j * t`. The explicit corollaries `rectangularMeasure_integer_cube` and
`rectangularMeasure_integer_cube_swap` take `S` to be the valuation integer
subring. They apply in the target's p-adic instance context and require only a
valued field, with no assumption that the scalar cube has mass one.

The provenance is internal finite-product measure theory, rather than a new
claim attributed to the JPSS original. Imports are limited to the two
published measure modules and pinned Mathlib's product-integral module.
The implemented route uses Mathlib's finite-coordinate measure-preserving
equivalence, Tonelli, integrable product domination, and Bochner Fubini.
Independent semantic review and publication are required before downstream
use as an accepted result.
