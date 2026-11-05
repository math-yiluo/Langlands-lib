# Original general-linear finite-smooth enveloping and center comparisons

For every number field and every natural rank, this internal comparison keeps
the original finite-smooth rational function carrier and the original matrix
enveloping and associative-center actions. The generic smooth scalar vector-field
commutator remains an explicit hypothesis. The atlas and its Lie group structure
are constructed from the supplied algebraic smoothness proof, in the same way as
the real differential comparison.

The full enveloping action comparison follows by injectivity of all original
finite slices. The actual finite-point homeomorphism supplies each slice
parameter. On every slice, the original function equivalence identifies actual
and matrix smooth functions. The actual finite slice law, the full infinite-place
action comparison and the original matrix slice law give identical slices. Thus
the unchanged finite-smooth function equivalence intertwines every actual tangent
enveloping differential with the original matrix action under
`GeneralLinearGroupPoints.infiniteEnvelopingEquiv`.

`generalLinearFiniteSmoothEnvelopingAction` is the actual action conjugated onto
the original carrier. It is proved equal as a complex algebra homomorphism to the
original action composed with that enveloping algebra equivalence. Restriction
to the actual associative center proves the corresponding function formula,
and `generalLinearFiniteSmoothCenterAction` is the conjugated center action.
Its algebra homomorphism equals the original center action composed with the
actual center equivalence. The equality proofs evaluate both homomorphisms and
use the function equivalence's inverse law. The local additive group on the
actual finite carrier is the standard one induced by its complex module.

These are internal consequences of the actual general-linear differential and
infinite-place enveloping comparisons, the actual adelic slice laws, and Worker
72's original matrix enveloping construction. No replacement function carrier,
supplied tangent identification, scalar commutator proof, growth estimate,
quotient-measure or reduction assertion is introduced.
