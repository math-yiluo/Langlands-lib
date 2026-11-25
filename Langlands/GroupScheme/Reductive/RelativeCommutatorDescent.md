# Descent and group operations for fppf-local commutator membership

This internal helper develops the predicate `RelativeDerived.LocallyCommutator` from the unchanged relative-derived input statement. It does not assert semisimple perfectness.

Restriction is proved by pulling back the witnessing jointly surjective flat locally finitely presented cover and mapping the abstract commutator subgroup under precomposition. Local membership on a cover descends by composing that cover with the witnessing covers of its members. These constructions use arbitrary indexed covers and impose no quasi-compactness condition.

The identity, inverse, and product lemmas then show that the predicate forms a subgroup of the group of points on each test scheme. For products the first cover is refined by a pulled-back witness for the second point. The provenance is the elementary functoriality of group commutators together with the cover composition and base-change operations in Mathlib; these are preparatory lemmas for the proof of `RelativeSemisimpleFppfPerfectStatement` (`relativeSemisimpleFppfPerfect` in `RelativeSemisimpleFppfPerfectProof`), rather than additional inputs assumed from the literature.
