# Literal norm and trace coefficients under unramified base change

Author: Worker 27.

This module is derived support for the prime norm argument. It uses the
published actual compositum, order, integer and residue maps. It does not
assert norm surjectivity. The new definitions and elementary compatibility
proofs are by Worker 27; the imported compositum norm and trace proof is by
Worker 159, and the imported relative maps and coordinates retain their
published authorship. No unpublished draft was reused.

`normTraceResiduePolynomial` in
`Langlands.PadicField.TopologicalData` constructs the polynomial
`residue(a) * X^ell + residue(b) * X - C(c)` from supplied integer
coefficients `a,b` and residue target `c`. Its evaluation formula is the
literal expression. If `1 < ell` and the residue of `a` is nonzero, its
natural degree is exactly `ell`: the first monomial has degree `ell`, the
linear term has degree at most one, and subtraction of a constant preserves
natural degree. For `a=1,b=0` it is exactly `X^ell-C(c)`.

For arbitrary source and target p-adic fields in independent universes,
`normTraceResiduePolynomial_map` identifies the polynomial obtained by the
actual `relativeResidueMap` with the polynomial built from the images of
`a,b` under `relativeIntegerMap` and the image of `c`. This is polynomial
equality, proved by mapping its displayed ring operations and reducing
the actual integer-map images. It is not inferred from equality of
functions on a finite field. Nonzero residues stay nonzero because the
relative residue map is an injective field map.

`ord_relative_algebraMap_of_equal_ramificationIndex` applies the published
relative order identity, substitutes equality of the two absolute
ramification indices, and cancels their nonzero integer value. It proves
order equality for every source field element, including zero with the
existing order convention. It allows every supplied order-one source
element to be used as a target uniformizer.

`Langlands.LocalClassField.totalUnramifiedCompositum_coefficientTransport`
applies `totalUnramifiedCompositum` to a finite totally ramified Galois
extension `E/F` and a finite extension `K/F` with equal absolute
ramification index. It keeps the returned linearly disjoint fields and the
same compositum `M`, equality `M.field = E.field sup K.field`, and inclusion
proofs `hE,hK`. It retains the degree, ramification-index, Galois, bijective
relative residue map, and `E`-element order and norm conclusions. It adds
the order comparison for `F -> K`, and applies the separately published
`totalUnramifiedCompositum_trace` to this same `M,hE,hK`.

The last two clauses use those genuine norm and trace identities on field
values. If a supplied source integer has field value
`N(E/F)(piE)^n / piF^n`, its actual integer image has field value
`N(M/K)(image(piE))^n / image(piF)^n`. If a supplied source integer has
field value `Tr(E/F)(piE^m) / piF^n`, its image has field value
`Tr(M/K)(image(piE)^m) / image(piF)^n`. The proofs preserve division and
powers, using the norm identity on `piE` and the trace identity on
`piE^m`. These clauses hold for all natural `n,m`, including zero, and
all supplied field elements. Source integrality is recorded by the
integer argument; no uniformizer or nonzero condition is needed for the
field equalities themselves. Applying them to the published graded norm
coefficients preserves the literal representatives.

This is an internal consequence of published arithmetic, not a new
original-source assertion. It proves neither break preservation nor
critical root existence nor the parent norm theorem. Those results have
their own statements and proofs. In particular it introduces no
assumption that a desired norm equation or coefficient compatibility
already holds: the two transport identities come from the published
compositum theorem and trace helper for the same actual fields.
