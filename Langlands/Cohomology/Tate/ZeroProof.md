# Degree-zero formulas for actual Tate cohomology

Authors: Worker 45 and Worker 120.
Worker 45 supplied the proof and its helper lemmas. Worker 120 audited the
proof against the published target and original source, added the complete
unapplied theorem check, and prepared this contribution for independent review.

The closing theorem `Langlands.Tate.zeroLaws` proves the complete
`Langlands.Tate.ZeroLaws` proposition, preserving its arbitrary carrier universe.
The proposition is published in `Langlands/Cohomology/Tate/ZeroStatement` and
is imported unchanged, together with its definition dependencies. The closing
assignment `example : ZeroLaws.{u} := @zeroLaws.{u}` checks the whole theorem
without supplying arguments or specializing the universe.

The proof uses the proved isomorphism from Mathlib's Tate cohomology in degree
zero to invariants modulo the actual norm image. Every class has an invariant
representative; its class vanishes precisely when it is a norm. This gives the
representative formula for the product of an equivariant bilinear coefficient
pairing and the formulas for subgroup restriction and corestriction.

The index identity reduces to the coset sum of a group-invariant vector.
Restriction preserves the pairing on representatives. For the projection
formula, bilinearity moves the finite coset sum through the pairing, and
equivariance plus invariance of its second argument identify the summands.

For coefficient naturality, the proof compares the actual map of Tate
complexes with the explicit short complex in degrees minus one, zero, and
one. `ShortComplex.LeftHomologyMapData` identifies the map on its kernel with
Mathlib's invariant functor, using the degree-zero cochain comparison.
The induced map on homology therefore commutes with the actual class map.
Surjectivity of the class map then reduces the naturality of the product,
restriction, and corestriction to their coefficient-level formulas. This
uses Mathlib's actual Tate coefficient maps throughout.

Sources: Serre, *Local Fields*, Greenberg translation, GTM 67 (1979),
Chapter VII, §7, printed pages 118–119; Chapter VIII, §§1–3, printed pages
127–132 (PDF pages 124–125 and 133–138). The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
These pages were read for this proof audit. The degree-zero quotient is on
printed pages 127–128, the subgroup formulas and index identity on pages
119 and 129–130, and the product normalization and extension to equivariant
bilinear pairings on pages 131–132. Serre treats abelian groups and integer
bilinear pairings. The general commutative scalar ring, arbitrary carrier
universe, explicit comparison with Mathlib's complex, and the representative
proofs of naturality and the projection formula are internal extensions:
they use only linearity, equivariance, and finite sums. No flatness, freeness,
or normality of the subgroup is required.

These degree-zero results do not establish the all-degree constructions or
their connecting-map signs.
