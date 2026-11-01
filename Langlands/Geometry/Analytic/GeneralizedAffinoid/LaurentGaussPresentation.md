# Affinoid presentation of the completed Gauss Laurent algebra

Author: Worker 84.

Let `K : Type u` be an ultrametric normed field and let `t > 0`, supplied as
`Fact (0 < t)`. This module equips the existing Gauss Laurent polynomial
algebra and its completion with compatible normed `K`-algebra structures.
When `K` is complete, it constructs an isometric bounded `K`-algebra
equivalence between the actual closed quotient

\[
  K\{t^{-1}X,tY\}/\overline{(XY-1)}
\]

and `CompletedGaussLaurent K t`. Here the two coordinate bounds are `t`
and `t⁻¹`, respectively. No independence of `t` from the value group is
required. The result therefore also applies to the completed Laurent
fields constructed in `LaurentGaussField` at independent radii. The field
structure under that additional hypothesis is supplied by the imported
module, not constructed here.

## Evaluation and uniqueness

`GaussLaurent.variableUnit` is the polynomial monomial with exponent one,
whose inverse has exponent minus one. Its integer powers are the monomials
with the corresponding exponents. For an ultrametric normed `K`-algebra
`B` and a unit `b : Bˣ`, `GaussLaurent.evaluate` evaluates each integer
power at `b`, using Mathlib's additive monoid algebra lift. If
`‖↑(b ^ n)‖ ≤ t ^ n` for every integer `n`, the finite ultrametric sum
bound makes this map contractive.

For complete `B`, `CompletedGaussLaurent.lift` extends that map continuously
to the completion. The extension is contractive, sends the variable to
`b`, and sends its inverse to `b⁻¹`. Contractivity is proved on the dense
polynomial subalgebra and extended using closedness of the norm
inequality.

`CompletedGaussLaurent.hom_ext` shows that two bounded `K`-algebra maps to
any normed `K`-algebra are equal if they agree on the variable. Their maps
on units agree on its integer powers; hence they agree on every Laurent
monomial. The monoid algebra lift equivalence gives equality on all
polynomials, and completion density gives equality everywhere. Target
completeness and ultrametricity are not hypotheses of this uniqueness
result.

## The actual quotient and comparison

`LaurentAnnulus.radii t` is the positive two-coordinate polyradius
`(t, t⁻¹)`. `relation` is `X₀ X₁ - 1`, and `presentation` uses the existing
`PresentedAffinoidAlgebra.ofRelations` construction. Its carrier is the
actual weighted Tate algebra modulo the closure of the ideal generated
by this relation, with the quotient norm.

The relation makes the quotient coordinates an actual unit
`coordinateUnit`. Their quotient norm bounds give the required integer
power bounds: use the first coordinate for nonnegative exponents and the
second for negative exponents. This argument also handles exponent zero
using the quotient's proved norm bound for one.

`toCompletion` evaluates the two Tate variables at the Laurent variable
and its inverse. Finite products satisfy the weighted monomial bound,
so Tate evaluation is contractive. It annihilates the displayed relation
and descends to the closed quotient. The existing quotient norm estimate
proves that the descended map is contractive.

For complete `K`, the quotient is complete.
`fromCompletion` is the contractive completed Laurent lift at
`coordinateUnit`. The two composites are the identity:

- On the completion, `hom_ext` reduces the assertion to the variable.
- On the quotient, surjectivity of the presentation map and the weighted
  Tate algebra coordinate uniqueness theorem reduce it to the two
  coordinates.

`LaurentAnnulus.equivalence` packages these actual inverse bounded maps.
Since both maps are contractive, `norm_equivalence` proves exact norm
preservation, and `isometry_equivalence` proves isometry.

## Provenance and scope

This is an internal comparison construction over the published
`LaurentGaussField`, `Relations`, weighted Tate `Evaluation`, and
`BoundedEquivalence.Definitions` interfaces. It is justified by the
explicit monoid algebra evaluation, completion density, relation descent,
coordinate uniqueness and quotient norm estimates described above; it
does not claim to formalize a numbered result from external literature.

The construction supplies an actual affinoid carrier for one Laurent
completion step. It does not construct scalar base change of a full
affinoid domain, strictification, a section on spectra, finite rational
pullback decompositions, or a proof of `Domain.FiniteRationalCoverStatement`.
