# Spectral small-displacement subgroups on rational quotients

Author: Worker 36.

This module constructs subgroups of actual bounded automorphisms from spectral
bounds on actual rational quotient sections. It is a local construction toward
the analytic automorphism topology; no topology is defined in this module.

For an element `a` of a normed commutative ring and a real number `r`,
`BanachSpectrum.SpectralBound a r` means that `x(a) ≤ r` at every point of the
bounded multiplicative spectrum. This universal inequality does not require a
maximum, a nonempty spectrum, or a nonzero ring. It is vacuous when the spectrum
is empty. It is a spectral bound, not a bound in the quotient norm.

The implemented elementary lemmas show that spectral bounds are monotone in the
radius, are unchanged by negation, and are preserved by every bounded unital ring
homomorphism. The latter proof pulls a target spectrum point back to a source
point. Over an ultrametric normed field, the published strong triangle inequality
for spectrum seminorms implies that the sum of two elements with the same
spectral bound has that bound.

For an actual presented strict affinoid `K`-algebra `P`, an element `b : P`,
and `r ≥ 0`, `spectralDisplacementSubgroup b r hr` is the subgroup of `Aut P`
whose elements satisfy

```text
∀ x : BanachSpectrum P, x(g.hom(b) - b) ≤ r.
```

The identity has zero displacement. For multiplication, the Lean proof writes
the displacement of `g * h` as
`g.hom(h.hom(b) - b) + (g.hom(b) - b)`. Bounded-map preservation and the
ultrametric inequality give the bound. For inversion it writes the displacement
as `g.inv(-(g.hom(b) - b))` and uses the inverse identity. No norm-isometry or
common operator-bound assumption is introduced. This construction and its
elementary lemmas need no completeness of `K`.

For the rational constructions, `K` is complete. Given a unit-radius rational
presentation `d`, the published `stabilizerSectionAction d` maps the setwise
stabilizer of the actual subset `d.locus` to bounded automorphisms of the actual
quotient `d.algebra`. `stabilizerSpectralSubgroup d b r hr` is the inverse image
of the displacement subgroup under this homomorphism.
`rationalSpectralSubgroup d b r hr` maps it into the ambient group `Aut P`
along the subgroup inclusion. Its membership theorem states exactly that an
automorphism preserves `d.locus` and that its constructed fixed-quotient action
on `b` has the spectral bound at every point of `BanachSpectrum d.algebra`.
There is no requirement to fix the rational presentation or its individual
points.

The ambient rational subgroup is contained in `locusStabilizer d`, is monotone
in the radius, and equals that stabilizer when `b = 0`.
`RationalSpectralTest K P` stores one actual rational presentation, one quotient
element, and one strictly positive real radius. A finite family of such tests
defines `finiteRationalSpectralSubgroup` by intersection. The membership theorem
spells out all domain-preservation and spectral inequalities. Concatenation of
finite families gives intersection, and the empty family gives the whole group.
A domain-preservation condition without a nonzero function can be represented
by the zero-section test with any positive radius. Finite index types have a
universe independent of the field. Trivial valuations, zero quotients, empty
rational loci, nilpotents, and zero numerator arity are not excluded.

The construction is derived from the local tests in Berkovich's unfinished
*Etale equivariant sheaves on p-adic analytic spaces* (1995–1996), section 1.1,
printed/PDF pp. 1–2. There the automorphism neighborhoods impose preservation of
finitely many compact analytic domains and spectral inequalities on finitely
many functions on each domain, with positive radii and non-strict inequalities.
Here repeated domain tests encode several functions on the same domain. The
underlying quotient construction comes from Berkovich,
*Non-archimedean analytic spaces*, Trieste lectures (2009), section 2.1 and
Definition 2.1.2 on p. 7, the bounded-morphism category in Definition 2.1.11 on
p. 8, and rational algebras in Definition 2.2.1 and Exercise 2.2.2(ii) on p. 9.

The present implementation is restricted to chosen unit-radius rational
presentations over a fixed strict affinoid base and `K`-linear automorphisms.
It does not yet construct all compact analytic domains, arbitrary analytic
functions on them, or automorphisms of the coefficient field. The source uses
pullback notation, while the Library's left section action uses the forward
algebra map and its left spectrum action uses inverse pullback. Replacing a
group element by its inverse leaves each constructed subgroup unchanged, by
the proved subgroup laws.

No claim is made here that these subgroups define the full analytic
automorphism topology, that conjugation transports arbitrary rational tests,
that they form a neighborhood basis in any preexisting topology, or that
quotient and spectral norms agree. Continuity of rational section orbits,
openness in a specified topology, structure sheaves, smooth section stabilizers,
and equivariant etale sites remain separate obligations.

The registered Equish source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The Trieste source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
