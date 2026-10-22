# Unit coefficients for compatible closure transport

Author: Worker 134.

`absoluteRestrictionCoefficientsIso K E` upgrades the existing
`absoluteRestrictionCoefficients K E` to an isomorphism of topological
representations. Its source is `absoluteUnits K` restricted along the actual
`Field.absoluteGaloisGroup.mapOfAlgebra K E`; its target is `absoluteUnits E`.
The forward morphism is exactly the existing coefficient morphism, by
`absoluteRestrictionCoefficientsIso_hom`.

Here `K` is a field and `E` an intermediate field of `AlgebraicClosure K`, in
an arbitrary common universe `u`. The embedding data are the supplied algebra
structure `Algebra (AlgebraicClosure K) (AlgebraicClosure E)` and scalar tower
over `K`. The coefficient construction needs no normality, finiteness, or
characteristic-zero hypothesis, and imposes no agreement with the canonical
embedding of `E` into its own closure.

## Implemented construction

`closureUnitLinearEquiv` applies the functor of units to `suppliedClosureEquiv`,
uses additive notation for those units, and restricts the integer-linear
equivalence to the project's lifted integer scalar ring. Its pointwise
forward-map certificate is `closureUnitLinearEquiv_apply`.
`closureUnitContinuousEquiv` is continuous in both directions because the
actual coefficient modules carry discrete topologies.

`absoluteRestrictionCoefficientsInverse` uses the inverse continuous linear
equivalence. Its equivariance proof applies the injective forward equivalence,
uses the already proved equivariance of `absoluteRestrictionCoefficients`,
and cancels the forward/inverse composites. The category isomorphism's two
inverse laws are the inverse identities of `closureUnitLinearEquiv` on each
unit. Thus no inverse or equivariance law is assumed.

With the additional assumptions `Normal K E` and `CharZero K`,
`closureSubgroupCoefficientsIso` presents this same isomorphism as the
coefficient map for `closureSubgroupEquiv`, acting on `absoluteUnits K`
restricted to `E.fixingSubgroup`. `closureSubgroupEquiv_comp_inclusion` gives
the continuous-homomorphism identity that inclusion after this group
equivalence equals the existing absolute Galois map. These are the exact
interfaces needed to apply generic continuous-cohomology transport.

## Provenance and limits

This is a derived internal construction from the preceding
`ClosureRestrictionTransport` module, the existing absolute coefficient map,
and Mathlib's unit and linear equivalence constructions. It implements the
compatible group/coefficient maps described by Serre, *Local Fields* (1979),
Chapter X, section 4, printed page 156 / PDF page 162, immediately before
Proposition 5. Worker 134 read this source directly, together with section 3
on continuous cochains. The registered source is `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`. No project
errata entry was present when checked.

This module proves the coefficient isomorphism for each supplied embedding.
It does not assert equality of cohomology maps for different embeddings,
construct a cohomology equivalence, or prove degree-two exactness. Existing
Library pairs are unchanged.
