# Split central directions and the reduced archimedean Lie algebra

Author: Worker 2. Namespace: `Langlands.Global.ArchimedeanGL`.

This module separates the real scalar matrix direction at every infinite place
from the published real archimedean matrix Lie algebra. It constructs the
complement, the positive-rank direct decomposition and the inclusions of the
existing compact algebra into the complement and its complexification. These
are concrete matrix constructions for `K : Type u` with `Field K`. They apply
to number fields in arbitrary universes. The algebraic definitions do not need
the additional `NumberField K` assumption or finite dimensionality.

## Trace condition and compact directions

`SplitCenterCoordinates K` is the product of real-valued functions on the real
infinite places and real-valued functions on the complex infinite places.
Thus it assigns one real scalar to each place, including each complex place.
`mixedRealPart` keeps the real-place values and takes the real part of the
complex-place values in the existing mixed archimedean algebra.
`mixedRealScalar` embeds those real scalars into that same mixed algebra.
Their composite is the identity on the scalar coordinates; real part is also
unchanged by coefficient conjugation.

`realTrace K n` composes the existing matrix-coordinate equivalence, matrix
trace and `mixedRealPart`. Its value at a real place is the real matrix trace,
and at a complex place it is the real part of the complex matrix trace.
`realTrace_lie` proves that the trace of every commutator has zero real part,
using the cyclic matrix trace identity. `realTrace_star` proves invariance
under the actual matrix star (transpose and coefficient conjugation).

`reducedLieSubalgebra K n` is the kernel of this real linear trace map,
with bracket closure supplied by `realTrace_lie`. The membership lemmas give
both the kernel equation and its exact coordinate meaning: zero trace at each
real place and zero real part of trace at each complex place. In particular,
imaginary scalar matrices at a complex place are retained.

`compactLieSubalgebra_le_reduced` proves that the existing skew-adjoint compact
algebra lies in this kernel. Applying real trace to `star X = -X` makes its
value equal to its own negative, hence zero over the reals. `compactToReduced`
is the resulting real Lie algebra inclusion. It retains the underlying matrix;
it introduces no new compact algebra or supplied compatibility assumption.
These constructions are valid for every natural rank, including zero.

## Scalar matrices and direct decomposition

`splitCenterScalar K n` sends the real coordinates to scalar diagonal matrices
through `mixedRealScalar` and Mathlib's `Matrix.scalarAlgHom`. The equation
`splitCenterScalar_matrix` gives that exact matrix formula.
`splitCenterScalar_lie` proves that these matrices commute with every ambient
matrix. Their linear range is `splitCenterSubmodule`; the same range with
bracket closure is `splitCenterLieSubalgebra`. The latter is central, as stated
by `splitCenterLieSubalgebra_central`. No claim that it is the entire center
is made: imaginary scalar directions at complex places lie elsewhere.

`realTrace_splitCenterScalar` gives the normalization
`realTrace (splitCenterScalar r) = n • r`. `splitCenterCoordinate` is real
trace multiplied by the real inverse of `n`. For `NeZero n`, its composite with
`splitCenterScalar` is the identity, so the scalar map is injective.
`reducedProjection` subtracts this scalar part from the original matrix and
proves that the result belongs to the reduced subalgebra.

For the same positive-rank hypothesis, `splitCenterDecomposition` is the
explicit real linear equivalence

`RealLieAlgebra K n ≃ₗ[ℝ] SplitCenterCoordinates K × reducedLieSubalgebra K n`.

It sends `X` to its normalized real trace and its reduced projection. Its
inverse sends `(r,Y)` to `splitCenterScalar r + Y`. Both inverse identities
are proved by the trace normalization and additive cancellation. The displayed
application and inverse-application lemmas expose these formulas. The
coordinate map itself is defined at rank zero, but the injectivity,
projection and decomposition assertions require `NeZero n`; no positive-rank
claim is silently extended to the empty matrix index type.

## Complex relative pair

`ReducedComplexLieAlgebra K n` is the actual scalar extension
`ℂ ⊗[ℝ] reducedLieSubalgebra K n`. `reducedComplexInclusion` complexifies the
real subtype inclusion into the full published `ComplexLieAlgebra K n`.
It is an injective complex Lie homomorphism; injectivity follows from flatness
of a real vector space under scalar extension.

`compactToReducedComplex` complexifies `compactToReduced`. Both maps have
explicit elementary-tensor formulas. `reducedComplexInclusion_compact` proves
that their composite is the existing `compactComplexInclusion`, by tensor
induction. Thus the same compact complex algebra sits inside this reduced
complex algebra and the ambient complex algebra with compatible inclusions.
The real trace condition is imposed before complexification. It is not imposed
as a non-complex-linear imaginary-trace condition on arbitrary elements of the
already complexified algebra.

## Source correspondence and limits

Laurent Clozel, *Motifs et formes automorphes: applications du principe de
fonctorialité*, in *Automorphic Forms, Shimura Varieties, and L-functions*,
Volume I (1990), printed pp.113–114, separates the split central direction
before introducing the relative pair with the standard compact group.
The last paragraph of p.113 describes the complementary trace as imaginary;
p.114 uses the compact group `O(n)` or `U(n)` and, in the proof of Lemma 3.14,
the subgroup with determinant of absolute value one. The present construction
implements the corresponding real matrix condition, followed by scalar
extension, and combines it over all infinite places.

Registered source:
`clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`.
Retained file:
`literature/Automorphic Forms, Shimura Varieties, and L-functions, Volume I (including Clozel, Motifs et formes automorphes).pdf`.
SHA256: `ed6ec30fc1f53f7c8ac4276ef449e1cad3ab42457bf5b7ee90a33413345ff96c`.
Worker 2 visually checked printed pp.113–114 (one-based PDF124–125) and verified
the retained fingerprint. No source-specific errata file was present in the
project or supplied Library notes.

The explicit trace maps, their kernels, scalar matrices, inverse formulas and
tensor inclusions are derived implementations using the published
`ArchimedeanLieAlgebra` and `ArchimedeanCompactLieAlgebra` modules and Mathlib's
matrix trace, scalar matrices, Lie subalgebra inclusion and scalar extension.
This unit does not construct the positive real central group, prove that its
tangent algebra is this scalar range, or identify the reduced algebra with a
determinant-level subgroup's tangent space. It constructs no compact group
action on cochains, relative cohomology, algebraic coefficient representation,
or comparison with Clozel's cohomology calculation. Those remain separate
prerequisites and theorem obligations; Lemma 3.14 is not asserted here.
