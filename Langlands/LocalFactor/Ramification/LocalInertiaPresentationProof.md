# Inertia surjectivity, finite presentations and conductor independence

`inertiaSurjectivityPresentationAndConductorIndependence` proves the nine
clauses of `InertiaSurjectivityPresentationAndConductorIndependenceStatement`
for every Mathlib nonarchimedean local field `K` and specified separable
closure `Ω`. The field, closure and two representation carriers have
independent universes. [Statement and conventions](LocalInertiaPresentationStatement.md)

## Inertia and finite presentations

An integer of `Ω` belongs to the finite Galois field obtained by adjoining
it and taking the normal closure. Its spectral norm is the same in that
field and in `Ω`, so it comes from the finite integer ring. An element of
the absolute upper group at zero restricts to finite inertia there. The
inclusion of the finite integer ring commutes with the automorphism action
and induces a residue homomorphism, so the automorphism fixes the residue
of the original integer of `Ω`. This puts the absolute upper group at zero
inside absolute inertia. The published `Wintenberger.localAbsoluteUpperFiniteImage`
then lifts every finite inertia element to absolute inertia. The degree-zero
inclusion into the Weil pullback gives the Weil lift, and the commuting
restriction square gives surjectivity between finite levels.
[Finite images of absolute upper groups](Wintenberger/Absolute.md)

The proof pulls a continuous Weil action back along the continuous inclusion
of absolute inertia. The Krull neighborhood basis gives nonarchimedeanness,
and `Weil.open_kernel_of_continuous_nonarchimedean_representation` gives an
open kernel on absolute inertia. A finite Galois fixing subgroup, intersected
with absolute inertia, lies in that kernel. Restriction to this finite field
therefore supplies the presentation condition. The action on Weil inertia
factors through the finite inertia of that field, which gives finite image.
[Continuity of complex representations](../../Weil/Representation/ContinuityProof.md)

## Conductor comparison

For an inertia representation at a finite level, the proof integrates the
codimension of the upper-group fixed space. Between `φ(i)` and `φ(i + 1)`
the fixed space is that of the lower group `G_(i+1)`. The width of the
interval is `|G_(i+1)| / |G_0|` by the finite Herbrand formula. The integral
from zero to any bound at or beyond the upper image of the lower cutoff is
therefore the Swan sum. The codimension is zero beyond the cutoff. The
Artin formula adds the codimension of the full inertia-fixed space at zero.
[Finite Herbrand functions](Herbrand/GeneralFinite.md)

For a nonnegative upper index, each finite upper group is the image of the
same absolute upper group, which lies in absolute inertia by monotonicity.
The descent evaluates on this image as the original Weil action evaluates
on the lift. This identifies the upper fixed subspaces of any two
presentations of one action. Integrating to a common cutoff proves Swan
independence, and comparing the values at zero proves Artin independence.
The proof casts the rational expressions into the reals and uses injectivity
of this cast to obtain the rational equalities.

Refinement is the comparison with the presentation at the larger field.
At the compositum, the published descent identity identifies each specified
pullback with the representation at its refined presentation. For equivalent
Weil actions, the intertwining linear equivalence transports the kernel
condition to the second carrier at the first presenting field. The existing
descent equivalence preserves both sums at that field, and independence
compares with the second presentation. [Descent of inertia actions](Descent.md)

## Sources

- Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
  Springer GTM 67 (1979), `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  I §7, Proposition 22(b), pp. 22–23 gives the inertia restriction sequence.
  IV §1, Propositions 1–2, p. 62 and IV §3, Proposition 14 and Remark 1,
  pp. 74–75 describe the inertia and upper groups and the inverse limit.
  VI §2, Proposition 2 and Corollary 1′, pp. 100–101 give the fixed-space
  formula, and Proposition 3 with its corollary, p. 101 gives invariance
  under inflation. The proof uses the upper fixed-space integral to compare
  the sums.
- Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des
  constantes locales d'équations fonctionnelles de fonctions L*, Invent.
  Math. 64 (1981), `deligne-henniart-1981-variation`, SHA-256
  `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
  §§0.4–0.5, pp. 91–92 identify Weil inertia, describe the finite inertia
  image and give the index-zero correction relating Artin and Swan.
