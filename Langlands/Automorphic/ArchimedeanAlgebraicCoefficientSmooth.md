# Smooth orbit maps of the actual archimedean algebraic coefficients

This internal construction continues the actual coefficient attachment in
`ArchimedeanAlgebraicCoefficient` using the reusable regular-function
smoothness criteria and Mathlib's real smooth calculus. The field retains its
independent universe and has a number-field structure. The finite selected
embedding index and coefficient matrix index are small. Empty indices and
rank zero are allowed.

`contMDiff_embeddingGL` proves real smoothness of every selected matrix-units
coordinate after the actual completion-to-mixed-coordinate equivalence. The
underlying real-linear map applies the genuine oriented embedding to every
matrix entry. Its finite-dimensional source gives continuity; composition
with the units value map and the open-embedding criterion gives smoothness
into the target GL manifold. The chosen complex conjugate orientation remains
the existing conjugate algebra homomorphism.

The full coefficient space inherits the supremum norm, complex normed-space
structure and completeness of all coordinate vectors. These structures use
the existing additive and complex-module operations.

`contMDiff_representation_matrix` derives smoothness of the genuine scheme
representation evaluated on those actual oriented group coordinates, using
`contMDiff_productMatrixPointsHom`. It assumes no separate regularity premise
for the representation.

For any real charted parameter space with independent model and parameter
universes, `contMDiff_representation_action` takes a smooth family of group
elements in the mixed matrix-units coordinates and a smooth family of
coefficient vectors. It proves smoothness of their actual coefficient action.
The proof first applies the matrix regularity result and the units value map.
Each output vector coordinate is the finite sum

```text
sum_b rho(embeddingGL(g(x)))_(a,b) * v(x)_b.
```

Matrix-entry and vector-coordinate maps are continuous real linear maps.
Real smoothness of complex multiplication, finite sums and coordinate
assembly proves the result on the entire coefficient space. No invariant
subspace or extra coefficient-action hypothesis is chosen.

`contMDiff_jointAction` specializes this result to the two projections from
the product of the actual mixed-coordinate group and the full coefficient
space. Its source model is the product of the matrix model and coefficient
model. `contMDiff_orbit` specializes it to the identity group family and a
constant vector, proving that every coefficient vector has a real smooth
orbit function on the actual completion-based group.

`smoothOrbitMap` is an actual complex-linear intertwining map

```text
Space e rho  -->  VectorSmoothFunctions F n (Space e rho)
v           |->  (g |-> representation e rho g v).
```

The target is the published subspace of genuine vector valued functions
whose pullback to mixed coordinates is real smooth. Its action is the
published right translation `R(h)f(g) = f(g*h)`. The representation
multiplication law proves

```text
smoothOrbitMap(rho(h)v) = R(h)(smoothOrbitMap(v)).
```

The application formula is definitional. Evaluation at the identity is the
original vector, so this intertwiner is injective. These are the statements
of `smoothOrbitMap_apply`, `smoothOrbitMap_one`,
`smoothOrbitMap_rightAction` and `smoothOrbitMap_injective`. No topology on
the smooth function space is supplied; injectivity is algebraic and follows
from actual function evaluation.

The provenance is internal: the published actual coefficient attachment,
oriented real algebra maps, archimedean coordinate equivalence, finite
group-scheme product criterion and GL regular-function criterion combine
with Mathlib's finite-dimensional continuity and smooth calculus. The
auxiliary `MatrixRepresentationProductSmooth` pair implements the generic
scheme-evaluation step. No new identification with an external source
definition is asserted.

Analytic identification of its differential with the previously constructed
dual-number differential, coefficient cohomology, highest-weight
classification and automorphic occurrence remain separate obligations.
