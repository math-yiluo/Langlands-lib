# Irreducible reduction from the two matrix analytic bases

`Langlands.GodementJacquet.genericMatrixFunctionalEquationReduction` proves the
internal `GenericMatrixFunctionalEquationReductionStatement`, with independent
field and actual representation-carrier universes. Its only two premises are
the unchanged closed Tate and higher-rank supercuspidal matrix
functional-equation statements. This conditional theorem supplies no proof of
either base and does not establish the unconditional host theorem.

The implemented proof first obtains a continuous scalar central quasicharacter
for each irreducible admissible factor. The published admissible Schur theorem
gives a locally constant character on the actual center. Composing with the
continuous homomorphism from field units to scalar matrices in that center
gives the required field quasicharacter. Its scalar action identity is the
Schur action identity evaluated at the same scalar matrix.

For a positive-rank irreducible supercuspidal factor, the proof splits the rank.
At rank one it applies the entire Tate statement using admissibility from the
supercuspidal predicate. At rank at least two it applies the entire
supercuspidal statement and packages its two polynomials, both equal to one,
as existential full matrix data. The supplied character, scalar additive Haar
measure and self-duality proof are retained in both cases.

Given the actual irreducible Whittaker-type representation in the conclusion,
the proof uses its admissibility and smoothness to form the corresponding
bundled smooth representation. Irreducibility supplies nontriviality of the
actual carrier through its simple group-algebra module. The published
`irreducible_supercuspidalProduct_embedding` then supplies a genuine injective
intertwining map from this representation into a canonical normalized product
of irreducible supercuspidal factors. The factor universe is chosen to be the
original carrier universe, independently of the field universe.

Each factor has admissibility and a scalar quasicharacter from the Schur step,
and full matrix data from the rank split. The finite-product theorem therefore
supplies full matrix data on the actual ambient normalized product. Its
smoothness is that of the actual normalized product induction functor.

To descend, the proof restricts the genuine intertwining map to its actual
range subrepresentation. Evaluating the intertwining field equation and using
subtype extensionality proves equivariance of this range restriction. It is
bijective by the original injection and the definition of the range, hence
gives an actual representation equivalence between the original source and
the range. Its inverse is a surjective intertwiner from that subrepresentation
to the original source. Actual-subquotient descent then constructs normalized
matrix data on that same source, including new normalized generator and
functional-equation parameters when needed.

The inherited conclusion is the unchanged full matrix-data predicate: both
common convergence half-planes, all actual test/coefficient rational
continuations, both normalized Laurent-span equalities with polynomial
constant coefficient one, Fourier witnesses before all coefficients, and the
guarded equation for every continuation pair. The supplied measure's square
product, plus transpose Fourier pairing, inverse-transpose coefficient,
normalized shifts, spectral variable, central scalar one and sign exponent
zero remain those of the imported definition. There is no added hypothesis on
a central character, chosen model, factor existence, or analytic data for the
original irreducible representation.

This proof is internal and derived from the imported Schur, classification,
finite-product and actual-subquotient theorems. It introduces no new assertion
from the literature.
