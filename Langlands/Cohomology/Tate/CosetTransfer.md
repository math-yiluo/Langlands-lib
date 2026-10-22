# Coset coordinates and the relative norm on coinvariants

Author: Worker 45.

For a subgroup `H` of `G`, fix the representatives supplied by the actual
left-coset quotient. `schreierElement H g q` is the subgroup element
`q.out⁻¹ * g * (g⁻¹ • q).out`. Its membership certificate is proved from
equality of the corresponding cosets. `cosetCoordinate H g` is
`g * (g⁻¹H).out`; it is proved equivariant for left multiplication by `H`.
On inverse chosen representatives it is the identity element. On their
products with `g` it gives exactly the displayed Schreier element.
It is an equivariant coordinate map; the chosen representative of the
identity coset need not be `1`, so no assertion that it fixes every
element of `H` is made.

For a representation `A`, `coinvariantsTransfer H A` is the genuine relative
norm from `A_G` to `A_H`: the class of `a` maps to the class of
`inverseCosetSum H A a` (from `InverseCosetSum`), the sum of `q.out⁻¹ • a`
over left cosets. The proof that this descends through
the full group coinvariant relations reindexes the coset sum and kills the
Schreier factors in `H`-coinvariants. Coefficient naturality is proved on
quotient representatives. Only finiteness of the coset space is required
for this construction; the carrier universe remains arbitrary.

These are internal coordinate constructions for the ordinary homological
transfer described by Serre, *Local Fields* (Greenberg translation, GTM 67,
1979), Chapter VII section 7, printed pages 118–119 (PDF pages 124–125),
and Chapter VIII sections 1–2, printed pages 127–130 (PDF pages 133–136).
Registered source `serre-1979-local-fields`, PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The quotient groups here are the actual coefficient coinvariants used by
Mathlib's resolution complexes. This pair makes no claim about Tate
cohomology.
