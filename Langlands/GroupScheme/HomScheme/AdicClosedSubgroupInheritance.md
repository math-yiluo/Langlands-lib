# Adic limits of torus subgroups pass to closed subgroups

`AdicClosedSubgroupInheritanceStatement.{u}` says that adic-limit bijectivity
for the small presheaf of actual closed torus subgroups passes through any
closed ambient subgroup inclusion in universe `u`.

Composition of closed inclusions gives a natural transformation on the small
presheaves. Its component at each test scheme is injective, since the closed
ambient inclusion is a monomorphism. For a compatible system inside the closed
subgroup, use adic effectivity in the larger ambient group. Its limiting torus
lies in the closed subgroup because this containment holds on every adic
restriction. The factorization remains a closed immersion, and injectivity of
the natural transformation recovers the prescribed system by restriction.

This is the actual closed-torus presheaf version of the inheritance in
Raynaud, SGA 3, Exposé XV, Proposition 8.7(ii), Gille–Polo recomposition,
PDF p. 60. The Lean proof uses the adic containment lemma on the limiting
torus over the complete local test.
