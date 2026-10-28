# The actual matrix trace Casimir in the complex enveloping center

Authors: Worker 94 and Worker 88. Module:
`Langlands.Global.ArchimedeanCasimirCartan`. All declarations are in
`Langlands.Global.ArchimedeanGL`.

This algebraic construction imports the generic invariant-form Casimir
from `Langlands.Algebra.LieCasimir` and the actual weighted trace and
positive Cartan forms from `Langlands.Global.ArchimedeanCartanTraceForm`.
It uses the unchanged matrix Lie algebra, its actual complexification and
its original universal enveloping algebra. It applies to an arbitrary
number field `K : Type u` and every natural rank `n`.

`realEnvelopingGenerator` composes the published real Lie homomorphism
`complexify` with the canonical complex enveloping generator restricted
to real scalars. Every real direction in the original matrix Lie algebra
is retained, including both real directions at a complex infinite place.
The scalar-tensor formula `envelopingGenerator_tmul` expresses a general
pure complex tensor generator as a complex scalar times this real
generator.

`matrixCasimir` applies the generic finite-sum construction to the actual
weighted real matrix trace form and this real generator. Finite
dimensionality is transported from the original matrix vector space; no
norm or topology is introduced. The choice of `Module.finBasis` implements
the sum, and `matrixCasimir_eq_sum` gives its value for every finite basis
and the actual trace-form dual basis.

Trace-form invariance and the generic commutator cancellation prove
`matrixCasimir_commutes_real_generator`. The complex centralizer of the
result is a complex subalgebra. It contains all real generators.
Tensor-product induction, the pure-tensor scalar formula and closure under
addition show that it contains the canonical generator of every element
of the actual complexified Lie algebra. Universal-enveloping generation
then implies that it contains every element of the complex enveloping
algebra. This proves `matrixCasimir_mem_center`, and
`matrixCentralCasimir` packages the same value in the published
`EnvelopingCenter`.

For each actual real matrix submodule, the restricted positive Cartan
form is symmetric and strictly positive on every nonzero vector.
Mathlib's algebraic orthogonal-basis theorem gives a finite orthogonal
basis. Multiply each vector by the inverse square root of its positive
self-pairing; each scalar is a unit. Bilinearity, the square-root identity
and orthogonality show that the new pairings are the Kronecker delta.
`cartanNormalizedBasis` chooses such a basis, and
`cartanNormalizedBasis_pair` gives the exact normalization. This uses
no inner-product or norm instance on the matrix carrier.

`compactCartanBasis` and `complementaryCartanBasis` apply that construction
to the actual compact Lie subalgebra and Cartan complement.
`cartanAdaptedBasis` combines their product basis with the inverse of the
published direct-sum equivalence. Its two index summands give exactly the
original inclusions of the two chosen bases. The within-subspace
normalization and imported cross-subspace orthogonality prove
`cartanAdaptedBasis_pair`. Symmetry of the trace form identifies its
dual basis with the stars of these basis vectors: pairing a starred
vector on the left with another basis vector is the reversed positive
Cartan pairing. `matrixTraceForm_dual_cartanAdaptedBasis` implements this
argument using Mathlib's exact dual-basis criterion. Empty subspace
bases require no special choice of a nonzero vector.

Explicitly, writing `e` for the adapted basis and `B` for the trace form,
the dual-basis criterion is
`B(star (e i), e j) = Q(e j, e i) = if j = i then 1 else 0`.
Thus its compact dual vectors are `-e i` and its complementary dual
vectors are `e i`.

`compactCartanSquareSum`, `complementaryCartanSquareSum` and
`cartanSquareSum` are respectively the sums of generator squares over
the compact, complementary and combined bases. For a compact basis vector,
star is its negative; for a complementary basis vector, star is the
vector itself. Substitute the adapted basis and its starred trace dual
into the basis-independent Casimir formula, split the sum into its two
index summands, and use real linearity of the generator. This proves
`matrixCasimir_eq_complementary_sub_compact`: the trace Casimir is the
complementary square sum minus the compact square sum.

The original complex compact enveloping subalgebra contains each real
compact generator, since it is the image of the pure tensor with scalar
one under `compactEnvelopingGenerator`. Closure under multiplication and
finite sums proves `compactCartanSquareSum_mem`.
`compactCartanElement` packages this same square sum in that actual
subalgebra. The full square sum is the compact sum plus the complementary
sum; rearranging the signed Casimir identity gives
`cartanSquareSum_eq_central_add_compact`. Thus the full square sum is the
inclusion of `matrixCentralCasimir` plus twice the inclusion of
`compactCartanElement`. The coefficient two is complex scalar
multiplication. This is an identity inside the original complex
enveloping algebra, and all basis directions are actual real matrix
directions. The terminology square sum refers to those algebraic squares
and the positive Cartan normalization; no order on the enveloping
algebra is asserted.

This is an internal algebraic construction from the stated imported
finite-sum identities and the actual complexification. No assumed
centrality certificate, substitute enveloping algebra or changed matrix
norm is used. All declarations retain an arbitrary number-field universe
and every natural rank. At rank zero the matrix Lie algebra and both
subspaces are zero-dimensional. Their bases are empty, all three square
sums and the Casimir are zero, and the same identities apply. Positivity
is used only to normalize existing basis vectors, so it imposes no
nonzero-dimensional hypothesis.

There is no differential principal-symbol
construction, elliptic regularity or automorphic growth theorem in this
module. Applying these algebraic identities to a genuine differential
action and proving ellipticity are separate subsequent obligations.
