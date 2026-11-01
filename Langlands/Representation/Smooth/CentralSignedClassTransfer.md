# Simple quotients from signed central class identities

This internal algebraic helper supplies the last generic sign and map
transfer step for an exact Grothendieck class identity. The coefficient
field, group and common representation carrier universes are independent.

Suppose the actual finite-length smooth representation `A` has a supplied
simple series on whose factors a central group element acts through
pairwise distinct scalars. Let `C` be another actual finite-length smooth
representation, and let `τ` be an actual irreducible smooth representation.
If there is a nonzero intertwiner `A → τ` and
`[C] = ε • [A]` for `ε = 1` or `ε = -1`, then `ε = 1` and there is an
actual surjective intertwiner `C → τ`.

`ofRepresentation_ne_neg_of_nonzero_simple_hom` proves the negative-sign
obstruction. The nonzero map makes the natural composition-factor
multiplicity of `τ` in `A` positive. The factor map sends exact classes to
actual finite sums of simple labels. Equality with a negative class would
make the nonnegative coordinate of `C` the negative of that positive count.
This argument does not require the central-series hypothesis.

`signedClass_eq_one_and_exists_surjective` separates the two possible
signs. In the positive case it applies the actual central-class quotient
transfer of `Smooth.CentralClassDetection`. In the negative case it applies
the preceding obstruction. `simpleQuotientOfSignedClass` chooses the
resulting actual surjective intertwiner and retains surjectivity in its type.

For group transport, `exists_scalarSeries_pullback` pulls a supplied simple
series through any group equivalence, with the same index set and scalar
function. The element at which the scalar action holds is the inverse
image of the original element. This uses the actual graded equivalences
from `groupEquivFiltrationMultiplicityTransport`.
`groupEquiv_central` proves centrality of that inverse image. Injectivity
of the unchanged scalar function is therefore retained for later central
class transfer.

The substantial inputs are `Smooth.CentralClassDetection`, which supplies
actual quotient maps across equality of centrally separated exact classes,
its genuine composition-factor sums and simple-map multiplicity detector,
and `Filtration.MultiplicityTransportProof`, which transports actual
series and their actual graded representations through group equivalences.
The provenance is their internal algebraic combination. All actual short
exact sequence relations, including nonsplit ones, are retained. There is
no parabolic, Aubert, irreducible-image or classification theorem input,
and no original literature statement is transcribed.

Author: Worker 1186.
