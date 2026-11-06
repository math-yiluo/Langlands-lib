# Actual torus-fibre maximality and zero-weight comparison

This internal module transports actual maximal tori through the natural
pullback-composition comparisons and through the prescribed etale residue-field
isomorphism. It also tests self-centralization in an original chosen geometric
fibre using a maximal torus in an arbitrary algebraically closed field-valued
fibre over the same point. The universal algebraically closed maximal-torus
centralizer statement remains an explicit input of this last comparison.

The field-valued fibre's standard torus factors through its actual identity
component. Maximality in the ambient fibre implies maximality in that closed
identity component. Reductivity follows from membership of the image in the
unchanged original locus. Applying the retained centralizer statement gives
self-centralization, hence the dimension of the actual zero adjoint weight is
the torus dimension. The identity-component inclusion identifies this weight
with the ambient weight. Actual exponent-weight base change equates that
dimension with the original relative zero-weight rank. The existing zero-rank
criterion then gives self-centralization in the original chosen geometric
identity component. No isomorphism of independently chosen algebraic closures
is assumed.

The definition
`splitTorus.identityComponentReductiveNeighbourhood_of_maximal_fieldPoint`
uses this original-fibre self-centralization to construct an actual open
neighbourhood of the field point's image contained in the unchanged reductive
identity-component locus. The universal field reflection, root reducedness,
root-line and maximal-torus centralizer statements remain explicit inputs,
together with the supplied closed relative standard torus and its maximality
at the algebraically closed field-valued point. It applies the existing
original-geometric-fibre field-input constructor after the zero-weight
comparison.

The provenance is internal composition of published actual pullback naturality,
maximality transport under source and ambient isomorphisms, maximality under a
field isomorphism, actual identity-component weights and the relative weight
rank comparison. These declarations do not construct a relative torus or prove
the universal openness statement. All constructions are uniform in universe
`u`, without characteristic, Noetherian or connected-ambient-fibre restrictions.
