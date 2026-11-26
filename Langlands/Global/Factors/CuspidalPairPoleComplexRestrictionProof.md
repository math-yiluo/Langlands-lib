# Complex Whittaker restriction surjectivity

`complexPlaceWhittakerRestrictionSurjectivity` proves
`ComplexPlaceWhittakerRestrictionSurjectivityStatement` over number fields in
universe `u` with compact additive adelic quotient. It gives restriction
witnesses for both compatible characters at the supplied complex place and
standard-module parameter of a cuspidal realization trivial on the split centre.

For the character of scale \(a\), `complexPlaceWhittakerRange` realizes each
function in the specified local model by an actual cuspidal vector at the
chosen place. The range theorem constructs a coefficient map from the
compact-finite standard module by restricting adelic Whittaker functions. It
uses the nonzero value at the identity and exact complex Whittaker
multiplicity one to identify the range of the map with the specified model.
[Complex-place range proof](../RankinSelberg/ComplexPlaceWhittakerRange.md)

To obtain `IsComplexPlaceWhittaker`, the proof pairs the vector with the
identity finite adelic coordinate. Its image under `finitePoint` is the
identity adelic point, so function extensionality gives the required equality
from the range theorem's pointwise formula.

For scale \(-a\), `inverseCharacter_rational` gives triviality of the inverse
adelic character on the diagonal field. The proof compares the circle values
after coercion to \(\mathbb C\), where `complexComponent_complex_inv` verifies
compatibility at scale \(-a\). The range theorem then gives a vector for the
inverse character with the identity finite coordinate. The rewrite
`complex_inverseCharacter` puts its Whittaker coefficient in the form
required by the second clause.
