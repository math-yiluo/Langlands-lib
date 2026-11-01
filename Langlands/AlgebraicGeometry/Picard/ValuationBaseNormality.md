# Normal stalks of a valuation spectrum

This internal adapter records the ring properties of the actual
structure-sheaf stalks of an affine scheme. It is a prerequisite for the
valuation-base part of the two-axis extension argument.

`Langlands.AlgebraicGeometry.HasNormalStalks S` is the proposition that, for
every point `x` of `S`, the ring `S.presheaf.stalk x` is a domain and is
integrally closed. The definition uses the actual stalk ring; it does not
choose an isomorphic localization as a replacement.

`spec_hasNormalStalks` proves this predicate for `Spec R` when `R` is an
integrally closed domain. Mathlib supplies the algebra structure and
prime-localization property of each affine stalk. The proof applies
`IsLocalization.isDomain_of_atPrime` to obtain its domain property and
`isIntegrallyClosed_of_isLocalization` to obtain integral closedness.
The complement of the prime ideal lies in the nonzero divisors, as required
by the latter theorem.

`valuation_spec_hasNormalStalks` specializes this result to a valuation
domain. Mathlib's valuation-ring instance supplies a Bezout domain, whose
integral closedness is available through typeclass inference. The universe
is arbitrary. There is no rank, noetherianity or discreteness assumption,
and fields are included.

The provenance is internal: the predicate packages two existing Mathlib
ring properties, and the proofs specialize the existing localization
results to the canonical affine stalks. This module does not define or
prove geometric unibranchness, extend a section or line bundle, or prove
`ValuationRingTwoAxisExtensionStatement`.
