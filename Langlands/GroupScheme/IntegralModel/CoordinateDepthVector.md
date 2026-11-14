# Vector depth models with independent real coordinate offsets

For a surjective integer-valued valuation on a field `K`, its valuation ring
`R`, and fixed real offsets `offset j`, the model at real depth `r` is the
polynomial vector group over `R` with generic coordinate `j` multiplied by
a chosen scalar of integer depth `ceil(r - offset j)`. These scalars are
nonzero and attained by surjectivity. The generic identification is the
actual diagonal group-scheme isomorphism. All models are smooth with
geometrically connected fibres, in every finite dimension, including zero.

The diagonal lattice membership lemma proves that the image of integral
points has precisely the separate coordinate valuation bounds
`v(x j) ≤ exp(-ceil(r - offset j))`. The forward implication uses that each
integral coordinate has value at most one. In the reverse implication,
division by the chosen nonzero scale gives an element of the valuation
ring in each coordinate. For the existing Henselian normalized additive
valuation, these bounds are equivalent to
`r - offset j ≤ henselianIntegerAddValuation(x j)`.
Henselianity is used only to invoke that additive valuation API.

For `r ≤ s`, each quotient of the depth `s` scale by the depth `r` scale
is integral, by monotonicity of the integer ceiling. Applying the diagonal
transition to these coefficients constructs an actual integral model map
extending the identity on the generic vector group. Every other extension
of that identity equals it by flat generic rigidity. The diagonal kernel
theorem therefore proves smoothness, connectedness of the underlying
scheme and representation-theoretic unipotence of its actual
scheme-theoretic special-fibre kernel. The coordinate coefficients may
vanish independently after reduction. Equal depths and mixed jumps are
included.

An actual group-scheme isomorphism from a generic group to the standard
vector group transports the family, the exact point bounds and the
every-extension kernel theorem to that generic group. Natural vector
coordinates on every scheme test provide such an isomorphism. In that
case the point bounds are proved in the original section coordinates,
evaluated through the canonical field global-sections isomorphism.
This transport uses scheme isomorphisms, not only rational-point maps.

The provenance is internal valuation algebra and transport, generalizing
the uniform depth family and using the independently scaled vector
models. The motivating source is Kaletha–Prasad, *Bruhat–Tits theory:
a new approach* (2023), Section C.2 and Fact C.2.1, printed pp.697–698 /
PDF pp.728–729, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The coordinate-offset
construction and its proof are derived infrastructure. No assertion
identifies a ramified field lattice with these coordinate bounds or
compares the family with an arbitrary supplied apartment filtration.
