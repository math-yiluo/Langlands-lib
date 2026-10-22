# Functorial laws for twisted intertwiners

`Langlands.TwistIntertwiningCompatibility` is a proposition definition over a
commutative ring `R`, a group `G`, and three arbitrary `R`-modules `V`, `W`, `U`.
Their universes are independent. For every unit-valued homomorphism `chi` and
representations `rho`, `sigma`, `tau` on these modules, it states:

1. `twistIntertwining` preserves the identity and composition of intertwiners.
2. `untwistIntertwining` preserves the identity and composition of intertwiners
   between representations with a common twist.
3. `twistEquiv` preserves reflexive equivalences, inverses, and composition.
4. The intertwiner underlying a twisted equivalence is the twist of its
   underlying intertwiner.

The order of intertwiner composition is Mathlib's: `g.comp f` applies `f`
first. Equivalence composition is written `e.trans f` and applies `e` first.
All equalities compare morphisms between exactly the same representations.
There are no hypotheses of continuity, smoothness, finite dimensionality,
irreducibility, or unitarity.

## Provenance

These are internal structural consequences of the accepted twist constructions.
Both twisting and removing a common twist retain the underlying linear map,
while twisting an equivalence retains its underlying linear equivalence.
Consequently the displayed identity, composition, inverse, and projection
operations agree on every vector. This statement records the laws needed to
reuse those constructions with Mathlib's existing morphism interfaces.
It does not introduce a separate representation category or assert any
local Langlands compatibility.

The scalar convention is the one already documented and reviewed in
`Definitions.md`, motivated by Henniart 2000, Section 1.2(2), printed page 440.
These arbitrary-ring morphism identities are derived infrastructure; they are
not attributed to Henniart as a separate theorem.

- Literature ID: `henniart-2000-simple-proof`.
- Exact source SHA-256:
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Locator: Section 1.2(2), printed page 440 (PDF page 2), scalar twist convention.
- Retained original:
  `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.

## Exact dependencies

- Twist definitions: artifact `c83db975-8b79-4fbb-9901-2db836910a0a`,
  version 1, published at `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
- Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
  Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
- Pinned Mathlib interface:
  `Mathlib/RepresentationTheory/Intertwining.lean`, definitions
  `IntertwiningMap.id`, `IntertwiningMap.comp`, `Equiv.refl`, `Equiv.symm`,
  and `Equiv.trans`.

This pair specifies a target; it supplies no accepted proof.
