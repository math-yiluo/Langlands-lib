# The negative outer quotient with explicit compact-slice formulas

This module constructs an actual replacement quotient for all
linked negative-inner data using the interlaced equivalence from
`RealVisibleInterlaced`. It retains that equivalence's canonical two-Frobenius
word on each compact rank-three slice. The earlier quotient construction and
all its published files are unchanged; no equality with its chosen
interlaced equivalence is assumed.

Use the notation of `RealInducedPairNegativeOuterQuotient`: h=|innerWeight|,
L=|d.weight|, P=outerWeight, outer source R=[character x,induced rawOuter,
character v], exposed source R'=[induced rawOuter,character x,character v]
and heavier two-block `replacementPair`. The proved interlacing distance
for x inside the outer block is m=L−h, with 0<m<P and x.parity=0.

`localEquiv` is the equivalence [x,rawOuter]≃[rawOuter,x] chosen from the
stronger existence statement retaining the actual Frobenius formula.
`expose` extends it through the final character v using the published actual
standard equivalence in stages. `expose_exact` proves its exact intertwining.
The maps `sourceSlice` and `exposedSlice` restrict to the three middle
coordinates on every compact coset. `expose_slice` identifies each target
slice with `localEquiv` applied to the source slice;
`expose_symm_slice` proves the corresponding inverse identity.

If m is even, `expose_forward_formula` states that each slice of `expose f`
is exactly the canonical second-tail map followed by its generic map applied
to the source slice. If m is odd, `expose_inverse_formula` gives the canonical
first-tail/first-generic formula for each slice of `expose.symm f`. These are
the literal actual `IsBlockFrobData` witnesses of `RealVisibleInterlaced`,
with all symmetry signs and multipliers preserved. `HasSliceFormula` packages
both parity branches. There is no formula replacing the inverse by an
inverse-tail multiplier.

`quotient` applies `expose`, then the actual ascending inner tail in R', then
the published equality transport to `replacementPair`. Every step is an
exact intertwiner. The equivalence, the explicit right inverse of the inner
tail and the equality transport make this quotient surjective.
`ker_quotient` identifies its kernel with the exposed inner-binomial range
pulled back through `expose`. The proof uses the published tail/binomial
kernel equality and injectivity of equality transport.

`RealInducedPairVisibleOuterQuotientStatement` asserts exactness,
surjectivity, this kernel description and `HasSliceFormula` for all linked
negative-inner data. `realInducedPairVisibleOuterQuotient` proves it without
an outer-square or additional parity hypothesis.

This strengthens the concrete information available for a canonical
mixed-word comparison. It does not prove that the mixed-source filtration map
carries the quotient kernel into the earlier swapped-pair image. It does not
assert a full braid or the unrestricted two-induction-block filtration.
