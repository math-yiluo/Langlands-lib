# Elementary calculus of representations with strict affinoid tests

Author: Worker 36.

`Langlands.Analytic.StrictTestDomain.CalculusStatement` is a proposition
over every complete ultrametric normed field `K`. It groups four consequences
of the published `Represents` predicate on actual presented strict affinoid
algebras and their bounded algebra maps. This file states these consequences
without proving them.

1. **Identity.** The identity map of every presented strict affinoid algebra
   represents its whole bounded multiplicative seminorm spectrum.
2. **Transport.** For a bounded map `i : P → Q`, a bounded algebra equivalence
   `e : Q ≃ Q'`, and a subset `U` of the spectrum of `P`, the composite
   `e ∘ i` represents `U` if and only if `i` does. Both directions of the
   algebra equivalence are bounded; a merely algebraic equivalence is not
   sufficient input here.
3. **Unique comparison.** If `i : P → Q` and `i' : P → Q'` both represent
   the same subset `U`, there is exactly one bounded algebra equivalence
   `e : Q ≃ Q'` with `e ∘ i = i'`. The equivalence is a conclusion.
4. **Composition over an inverse image.** Suppose `i : P → Q` represents
   `U`, `W` is a closed subset of the spectrum of `P`, and `j : Q → R`
   represents the inverse image of `W` under the spectrum map of `i`.
   Then `j ∘ i` represents `U ∩ W`.

The composition clause quantifies over already specified actual maps `i`
and `j` and assumes their displayed representation properties. It does not
assert the existence of an algebra representing an arbitrary inverse image
or intersection. It needs no hypothesis that the spectrum map of `i` is
injective. The inverse-image formulation ensures that a factor through `i`
has spectrum image in the set represented by `j`. This is distinct from an
unrestricted transitivity assertion for any subset of the spectrum of `Q`.

All algebras and test objects have carriers in the coefficient universe,
with independently chosen finite Tate presentations. No nonzero-algebra,
reducedness or nontrivial-valuation assumptions are imposed. Every
representation assertion still tests only presented strict affinoids.

These are derived universal-property consequences of the restricted
definition, not separately quoted theorems of the original literature.
Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
printed/PDF page 8, Definition 2.1.11, supplies the contravariant
bounded-algebra-map convention. Page 9, Definition 2.2.1, supplies the
closed-subset, exact-image and unique-factorization requirements from which
the restricted `Represents` predicate was derived. The intended arguments
use identity factorization, transport by mutually inverse bounded maps,
uniqueness applied twice to obtain inverse comparison maps, and successive
factorization through `i` and `j`. Closedness in the last clause follows
from closedness of `U` and `W`; image equality follows by composing the
two image equalities.

The source's affinoid-domain definition tests all affinoids, even when
the representing algebra is strict. This statement retains the project's
explicitly weaker strict-test scope. It does not establish general
affinoid tests, arbitrary-radius constructions, inverse-image existence,
structure sheaves, analytic atlases or sites.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
