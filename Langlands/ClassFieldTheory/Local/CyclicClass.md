# Explicit cyclic classes

This module constructs a specific class in the actual relative group
cohomology of the multiplicative Galois module. It does not choose a local
invariant or assume a class-field-theoretic classification.

Let `n` be nonzero, let `chi : Gal(L/K) -> Multiplicative (ZMod n)` be a
homomorphism, and let `a` be a unit of `K`. Use the standard representatives
`r(g)` between zero and `n - 1`. The inhomogeneous 2-cocycle is

`(g,h) |-> a ^ floor((r(g) + r(h))/n)`,

where the base unit is included into `L` by its actual algebra map.
`cyclicCarry_spec` proves the division identity and `cyclicCarry_assoc`
proves the cocycle identity for the carries. `baseUnit_fixed` proves that
the Galois action fixes this coefficient. These certificates construct
`cyclicUnitCocycle` as an element of Mathlib's `groupCohomology.cocycles₂`.
`cyclicClass` then applies the actual quotient map `groupCohomology.H2π`.
No substitute cohomology group is introduced.

The carry is the integral coboundary of the rational lift `r(g)/n` of the
character `g |-> r(g)/n mod Z`: for the trivial action its differential is
`r(h)/n - r(gh)/n + r(g)/n`. `cyclicCarry_rational` proves the
corresponding rational identity in Lean. Thus the chosen positive generator has
character value `+1/n`. To obtain the arithmetic local normalization, a
later proposition applies this construction to the arithmetic Frobenius
coordinate on an unramified cyclic extension and to a uniformizer.
This module itself neither asserts the existence of such an extension nor
assigns an invariant to its class.

The base and extension fields have independent universes `v` and `u`.
The actual fields, automorphism group and unit groups are unchanged.
Coefficients use the explicitly lifted integer ring supplied by
`Cohomology`; no field resizing is involved.

## Original-source correspondence

The source is Jean-Pierre Serre, *Local Fields*, English translation,
GTM 67, Springer, 1979, retained as
`C:/Central-Library/Serre--Local Fields--1979.pdf`, registered source
`serre-1979-local-fields`.
The source SHA256 is
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

* Chapter VII, section 3, printed pp.112–113 (PDF pp.118–119), defines the
  inhomogeneous differential and the 2-cocycle equation. The carry formula
  above is the explicit differential of the stated rational lift; its
  division and cocycle certificates are derived implementation details.
* Chapter VIII, section 4, printed p.133 (PDF p.139), describes the
  generator character with value `1/n` and its boundary in `H²(G,Z)`.
  Sending the integer `1` to the fixed base unit gives the unit cocycle
  implemented here.
* Chapter XIII, section 3, printed p.193 (PDF p.198), defines the local
  invariant by valuation, the inverse connecting homomorphism, and
  evaluation at arithmetic Frobenius. This fixes the intended later use
  of the positive carry convention; no local invariant theorem is proved
  in this file.
