# From a type-A star cocycle to Hermitian discrepancies

Author: Worker 239.

This internal unit concerns the actual star field of supplied Tits index
data and a local special-linear presentation on a finite Galois cover.
Its construction is derived from the imported star-field, coordinate
change, inner-cocycle and Hermitian normalization results.

An automorphism of an embedded cover field lifts to the separable
closure by transporting it to the embedding's field range and applying
normal extension of automorphisms. The lift commutes with the original
embedding.

Under the identity/reversal star-image hypothesis, the actual star field
is separable quadratic. A cover automorphism that does not fix it
pointwise restricts to its nontrivial conjugation. This follows by lifting
the cover automorphism to the separable closure and applying the
established restriction theorem for the actual star action. Conversely,
the star-field conjugation extends to the Galois cover, again by normal
extension of automorphisms.

The main result, `HasStarDiscrepancy.exists_hermitian_coordinates`,
assumes a finite Galois cover `M/K`, an embedding of that cover into the
separable closure whose image contains the actual star field, and the
all-test `HasStarDiscrepancy` predicate for a supplied local presentation
`E`. It also assumes characters `χ` giving the diagonal split-torus
coordinates and the adjacent-character root restrictions, a positive
rank, and that the first simple vertex is distinguished. The star image
is exactly the identity and the nontrivial chain reversal. All fields
and schemes retain their arbitrary universe and characteristic.

Let `f` be the canonical embedding of the actual star field into `M` and
let `H` fix its image. The lift calculation identifies the elements of
`H` with those having trivial star action, so the supplied matrices give
inner discrepancies there. The endpoint weight theorem shows that these
matrices preserve the first coordinate line. The normalized-inner-cocycle
result therefore supplies an honest matrix cocycle with the same
all-test actions. Blockwise Hilbert 90 supplies a matrix `P` expressing
it as a coboundary, with zero entries between unequal character spaces.
Changing coordinates by `P` makes every discrepancy in `H` trivial and
retains the original diagonal split-torus formula on every test scheme.

The actual star field is separable quadratic and Galois. Extend its
nontrivial conjugation to `M`; this automorphism moves the star field,
so its discrepancy is outer. The coordinate-change formula supplies
its new outer representative. The imported Hermitian-descent theorem
then constructs an actual nonsingular Hermitian form `J` over the star
field. Every automorphism moving that field restricts to its quadratic
conjugation, so the image of `J.gram⁻¹` represents all those outer
discrepancies, on every relative test scheme and every cover point.
The theorem returns `P`, `J`, trivial discrepancy on the image fixer,
these outer actions, and the retained diagonal coordinates. The root
restriction input is used in the endpoint weight argument; the same
characters are retained throughout.

This is an internal composition of the imported results, with no new
literature claim. It assumes the initial special-linear star cocycle;
it does not construct that cocycle or the final natural matrix
presentation. It supplies the correction and Hermitian-form portion
of that presentation without any rank-one classification input.
