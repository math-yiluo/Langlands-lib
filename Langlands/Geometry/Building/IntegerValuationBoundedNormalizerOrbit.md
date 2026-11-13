# Finite apartment orbits of algebraically bounded normalizer sets

This internal derived unit uses the original integer-valued building datum,
normalizer, centralizer and apartment. A compatible valuative relation is
assumed on the arbitrary field. No topology is used.

First, the supplied centralizer is connected reductive by the published
split-torus centralizer theorem. The finite character-image theorem gives
finitely many representatives of a bounded centralizer subset modulo its actual
character kernel. That kernel fixes every apartment point by the supplied V6
compatibility. The orbit of the subset at a given apartment point is therefore
finite.

For a bounded normalizer subset, separate its elements by their classes in the
finite actual relative Weyl group. Choose one normalizer representative of each
class. Left translation of the bounded ambient subset remains bounded.
Reflection of boundedness along the closed centralizer immersion makes each
resulting centralizer subset bounded. The original normalizer orbit lies in the
finite union of the translated centralizer orbits, so it is finite.

`IntegerValuation.BoundedNormalizerOrbitStatement` quantifies over all of this
data at arbitrary universe `u`. It states that every ambient algebraically
bounded subset of the actual normalizer has finite orbit at each point of the
actual apartment. `IntegerValuation.boundedNormalizerOrbit` proves that
proposition by the argument above. The subset need not be a subgroup.

The provenance is internal: this composes the published character-image,
centralizer, relative-root and relative-Weyl results with the V6 law in the
existing integer-valued building datum. It introduces no additional geometric
axiom.

This proves the finite apartment-orbit part of the bounded-normalizer argument.
It does not assert finite group elements, finite building orbits under a general
bounded subgroup, a complete building metric, or a fixed-point theorem.
