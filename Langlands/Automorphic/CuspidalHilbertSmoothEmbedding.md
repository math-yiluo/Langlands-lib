# Genuine smooth vectors of the original cuspidal Hilbert completion

This internal construction retains two named analytic premises:
`CuspidalHilbertOrbitCoefficientStatement` and
`Archimedean.HilbertSmoothKernelStatement`. For an actual cuspidal realization
`T` of `GL_(r+1)`, a prescribed unitary central character and a supplied full
positive form `b` with its exact canonical determinant-band integral identity,
`coordinateHilbertRepresentation` restricts the already constructed full adelic
action to the infinite factor in the published mixed real manifold coordinates.
It acts on the original `b.finiteForm.HilbertCompletion`.

`toHilbert_isSmoothVector` proves genuine Hilbert-norm smoothness of the orbit of
every original canonical embedded vector. The real model is
`ArchimedeanMatrix F (r+1)` with the existing operator matrix norm; the infinite
matrix group is the actual group of units in that mixed real Banach algebra.
The number-field universe is arbitrary, the matrix rank is `r+1`, and `GL_1` is
included. The supplied form and completion are retained throughout.

The smooth-kernel premise turns a smooth scalar diagonal coefficient of a
unitary representation into a genuine smooth orbit. Unitarity identifies the
two-variable orbit kernel with that diagonal coefficient at `g⁻¹*h`. The actual
coefficient premise supplies a smooth scalar function when its full-band vector
is chosen to be the identity band embedding of the canonical source vector.
The exact band pairing values and the constructed action's exact translated
embedding values identify this function with the diagonal source coefficient.
This proves smoothness in norm, rather than weak smoothness alone.

`toHilbertSmooth` is the complex-linear map into the genuine smooth-vector
submodule whose underlying map is the original canonical `b.finiteForm.toHilbert`.
The generic `linearSmoothEmbedding` is exactly its codomain restriction. The
generic `linearSmoothEmbedding_injective` proves injectivity whenever that
original linear map is injective; the published canonical Hilbert embedding has
that property. No new topological structure on the original algebraic carrier
or on the smooth-vector submodule is introduced here.

The module also supplies scalar derivative helpers for the subsequent generator
comparison. `inner_lieDerivative` is the real manifold chain rule for the bounded
linear functional `inner ℂ w (-)`. `ScalarCoefficientValues` records actual source
orbit pairings through a prescribed target map. `ScalarGeneratorLifts` requires
scalar functions with exactly those values and a first generator derivative at
the identity. `RealGeneratorCompatibility` is the equation between original
vector operators and genuine Hilbert orbit derivatives. The generic implication
from the first two predicates and genuine smoothness uses inner-product
separation. The identity-point normalization is proved first for an arbitrary
real Banach algebra; `smoothCoefficient_generator_one` applies the published
actual differential geometry formula with the original real matrix direction.

The provenance is internal composition of the supplied actual translated
embeddings, unitary action, named kernel criterion and actual coefficient
premise. The kernel criterion is still an explicit premise, rather than a
new proof of Neeb's theorem. This module proves no derivative-topology density,
Whittaker uniqueness or unconditional operator multiplicity one.
