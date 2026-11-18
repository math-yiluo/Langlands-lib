# The actual adelic Hilbert action from smooth scalar coefficients

This is an internal conditional construction for cuspidal operator multiplicity
one. Let `F` be any number field in universe `u`, with the project's compact
`AdeleQuotient` convention, and let `T` be an actual cuspidal operator realization
of `GL_(r+1)`. Retain a prescribed central character `χ` of norm one, a supplied
full positive form `b`, and the exact equality of its inner product with the
canonical quotient Haar integral restricted to `1 < |det| < 2`. The named
`CuspidalHilbertOrbitCoefficientStatement` is also an explicit input. It is an
unproved statement about actual smooth joint-finite scalar coefficients and
full enveloping covariance, rather than an assumption of image invariance.

`adelicHilbertRepresentation` constructs a group homomorphism from the full actual
adelic matrix group into bounded complex-linear operators on the original
`b.finiteForm.HilbertCompletion`. No replacement completion or transported form is
used. Its `adelicHilbertEmbeddingFamily` consists of the specified actual
translated embeddings into the unchanged full band `L²` space.

The generic Prop-valued predicate `UnitaryEmbeddingFamily.RealizesEmbeddings J U`
means both `J(1)(U(a)x) = J(a)x` for every completed vector and preservation of the
original source inner product by every `U(a)`. The theorem
`adelicHilbertRepresentation_realizes` proves precisely these properties for the
constructed action and the actual translated family. Since every `J(a)` agrees
with the translated quotient function on the canonical dense original carrier,
this retains the actual functions, as well as the group multiplication law.
The group inverse and unitarity also give surjectivity of each operator by the
generic embedding-family construction.

The proof first factors an arbitrary adelic element into its infinite and finite
parts. Positive right translation by it equals infinite translation of the
original finite-translated vector, which still belongs to the source carrier.
The earlier analytic-annihilator reduction, under the coefficient premise, thus
places every translated original vector in the original band image closure.
The actual identity embedding has exactly that closure as its range. A generic
dense-carrier argument extends containment to every completed vector, because
an isometric image of the complete source is closed. The actual completed Gram
identity then supplies a coherent `UnitaryEmbeddingFamily`. Transport through
the inverse of the identity embedding on its actual range constructs the group
homomorphism. The final two properties are packaged generically before the
actual specialization to keep the same Hilbert types and operators throughout.

All provenance is internal composition of the actual band constructions,
analytic closure reduction, finite/infinite adelic factorization and generic
coherent-isometry construction. There is no new external-source theorem claim.
The module proves no continuity in the adelic group variable, differentiable
smooth-vector or generator comparison, fixed-level derivative density,
Whittaker uniqueness or unconditional cuspidal operator multiplicity one.
